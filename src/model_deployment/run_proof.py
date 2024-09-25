from __future__ import annotations
import os
from typing import Any, Optional
import argparse
import json
import yaml
import pickle
from tqdm import tqdm
from dataclasses import dataclass
from pathlib import Path

from data_management.splits import FileInfo, Split, DataSplit
from data_management.dataset_file import Term, DatasetFile
from model_deployment.classical_searcher import ClassicalSuccess, ClassicalFailure
from model_deployment.prove import run_proof, RunProofConf, LocationInfo
from model_deployment.straight_line_searcher import (
    StraightLineSuccess,
    StraightLineFailure,
)
from model_deployment.whole_proof_searcher import (
    WholeProofSuccess,
    WholeProofFailure,
)
from model_deployment.searcher import (
    SearcherConf,
    searcher_conf_from_yaml,
)

from model_deployment.tactic_gen_client import (
    TacticGenConf,
    tactic_conf_update_ips,
    tactic_gen_conf_from_yaml,
    tactic_gen_client_from_conf,
)
from model_deployment.conf_utils import (
    wait_for_servers,
    start_servers,
    tactic_gen_to_client_conf,
)

from data_management.sentence_db import SentenceDB
from util.util import get_basic_logger, clear_port_map, set_rango_logger
from util.constants import CLEAN_CONFIG, RANGO_LOGGER

import logging

_logger = logging.getLogger(RANGO_LOGGER)


@dataclass
class TheoremLocationInfo:
    theorem_name: str
    test_file: Path
    data_loc: Path
    sentence_db_loc: Path
    data_split_loc: Path
    occurance: int = 0

    def get_file_from_split(
        self,
        data_split: DataSplit,
    ) -> tuple[FileInfo, Split]:
        resolved_test_file = self.test_file.resolve()
        resolved_data_loc = self.data_loc.resolve()
        for split in Split:
            for file_info in data_split.get_file_list(split):
                info_path = resolved_data_loc / Path(file_info.file)
                if info_path == resolved_test_file:
                    return file_info, split
        raise ValueError(
            f"Could not find data points file corresponding to {self.test_file}"
        )

    def get_dp_idx(self, dp: DatasetFile) -> int:
        num_found = 0
        for i, proof in enumerate(dp.proofs):
            if self.theorem_name == proof.get_theorem_name():
                if num_found == self.occurance:
                    return i
                num_found += 1
        raise ValueError(
            f"Occurance {self.occurance} of {self.theorem_name} not found in {self.test_file}"
        )

    def to_location_info(self) -> LocationInfo:
        data_split = DataSplit.load(self.data_split_loc)
        file_info, split = self.get_file_from_split(data_split)
        sentence_db = SentenceDB.load(self.sentence_db_loc)
        file_dp = file_info.get_dp(self.data_loc, sentence_db)
        idx = self.get_dp_idx(file_dp)
        return LocationInfo(
            self.data_loc, file_info, split, file_dp, idx, sentence_db, data_split
        )

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> TheoremLocationInfo:
        if "occurance" in yaml_data:
            occurance = yaml_data["occurance"]
        else:
            occurance = 0
        return cls(
            yaml_data["theorem_name"],
            Path(yaml_data["test_file"]),
            Path(yaml_data["data_loc"]),
            Path(yaml_data["sentence_db_loc"]),
            Path(yaml_data["data_split_loc"]),
            occurance,
        )


@dataclass
class TestProofConf:
    theorem_location_info: TheoremLocationInfo
    search_conf: SearcherConf
    tactic_conf: TacticGenConf
    print_proofs: bool
    print_trees: bool

    def update_ips(self, port_map: dict[int, tuple[str, int]]):
        tactic_conf_update_ips(self.tactic_conf, port_map)

    def to_run_conf(self) -> RunProofConf:
        return RunProofConf(
            self.theorem_location_info.to_location_info(),
            self.search_conf,
            tactic_gen_client_from_conf(self.tactic_conf),
            self.print_proofs,
            self.print_trees,
        )

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> TestProofConf:
        return cls(
            TheoremLocationInfo.from_yaml(yaml_data["thm_info"]),
            searcher_conf_from_yaml(yaml_data["search"]),
            tactic_gen_conf_from_yaml(yaml_data["tactic_gen"]),
            yaml_data["print_proofs"],
            yaml_data["print_trees"],
        )


PROOF_KEYWORDS = ["Lemma", "Theorem", "Proposition", "Remark", "Example", "Property"]


def get_term(dp_file: DatasetFile, theorem_str: str) -> Term:
    for proof in dp_file.proofs:
        if proof.theorem.term.text.strip() == theorem_str.strip():
            return proof.theorem
    raise ValueError(f"{theorem_str} not found in {dp_file.file_context.file}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser("Run a proof using a proof config.")
    parser.add_argument(
        "--conf_loc", required=True, type=str, help="Path to the config."
    )
    set_rango_logger(__file__, logging.DEBUG)

    args = parser.parse_args()
    conf_loc = Path(args.conf_loc)
    assert conf_loc.exists()
    with conf_loc.open("r") as fin:
        yaml_conf = yaml.safe_load(fin)
    conf = TestProofConf.from_yaml(yaml_conf)

    _logger.info(f"Starting tactic client.")
    tactic_client_conf, next_server_num, commands = tactic_gen_to_client_conf(
        conf.tactic_conf, 0
    )

    if 0 < len(commands):
        clear_port_map()
        procs = start_servers(commands)
        port_map = wait_for_servers(next_server_num)
        tactic_conf_update_ips(tactic_client_conf, port_map)
    else:
        procs = []

    new_conf = TestProofConf(
        conf.theorem_location_info,
        conf.search_conf,
        tactic_client_conf,
        conf.print_proofs,
        conf.print_trees,
    )

    _logger.info(f"Running proof.")
    try:
        result = run_proof(new_conf.to_run_conf())
        match result:
            case ClassicalSuccess():
                print(result.successful_candidate.proof_str)
            case ClassicalFailure():
                print("failed")
            case StraightLineSuccess():
                print(result.successful_proof.proof_text_to_string())
            case StraightLineFailure():
                print("failed")
            case WholeProofSuccess():
                print(result.successful_proof.proof_text_to_string())
            case WholeProofFailure():
                print("failed")
    finally:
        for p in procs:
            p.kill()
