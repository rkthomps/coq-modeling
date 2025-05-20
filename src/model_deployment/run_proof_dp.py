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
    StartModelCommand,
)

from evaluation.find_coqstoq_idx import get_thm_desc
from coqstoq.eval_thms import EvalTheorem
from coqstoq import get_theorem

from data_management.sentence_db import SentenceDB
from util.coqstoq_utils import get_file_loc, get_workspace_loc, str2split
from util.util import get_basic_logger, clear_port_map, set_rango_logger
from util.constants import CLEAN_CONFIG, RANGO_LOGGER

import logging

_logger = logging.getLogger(RANGO_LOGGER)

# I should be able to give 
# data_loc
# workspace_loc
# file_loc
# dp_name


@dataclass
class TestDPProofConf:
    data_loc: Path
    file_loc: Path
    workspace_loc: Path
    dp_loc: Path 
    thm_name: str # Could add line number for unambiguity
    sentence_db_loc: Path
    search_conf: SearcherConf
    tactic_confs: list[TacticGenConf]
    print_proofs: bool
    print_trees: bool

    def find_proof_idx(self, dp: DatasetFile) -> int:
        names = [p for p in dp.proofs if p.get_theorem_name() == self.thm_name]
        if len(names) == 0:
            raise ValueError(f"Proof with name {self.thm_name} not found in dataset file.")
        if len(names) > 1:
            raise ValueError(f"Multiple proofs with name {self.thm_name} found in dataset file.")
        return names[0].proof_idx
    
    def update_ips(self, port_map: dict[int, tuple[str, int]]):
        for conf in self.tactic_confs:
            tactic_conf_update_ips(conf, port_map)


    def to_run_conf(self) -> RunProofConf:
        sentence_db = SentenceDB.load(self.sentence_db_loc)
        dp = DatasetFile.load(self.dp_loc, sentence_db)

        location_info = LocationInfo(
            self.data_loc,
            self.file_loc,
            self.workspace_loc,
            dp,
            self.find_proof_idx(dp),
            sentence_db,
        )

        return RunProofConf(
            location_info,
            self.search_conf,
            [tactic_gen_client_from_conf(conf) for conf in self.tactic_confs],
            self.print_proofs,
            self.print_trees,
        )
    
    @classmethod
    def from_yaml(cls, yaml_data: Any) -> TestDPProofConf:
        data_loc = Path(yaml_data["data_loc"])
        file_loc = Path(yaml_data["file_loc"])
        workspace_loc = Path(yaml_data["workspace_loc"])
        dp_loc = Path(yaml_data["dp_loc"])
        thm_name = yaml_data["thm_name"]
        if "tactic_gen" in yaml_data:
            tactic_gen_confs = [tactic_gen_conf_from_yaml(yaml_data["tactic_gen"])]
        elif "tactic_gens" in yaml_data:
            tactic_gen_confs = [
                tactic_gen_conf_from_yaml(conf) for conf in yaml_data["tactic_gens"]
            ]
        else:
            raise ValueError("No tactic_gen or tactic_gens in yaml_data.")
        return cls(
            data_loc,
            file_loc,
            workspace_loc,
            dp_loc,
            thm_name,
            Path(yaml_data["sentence_db_loc"]),
            searcher_conf_from_yaml(yaml_data["search"]),
            tactic_gen_confs,
            yaml_data["print_proofs"],
            yaml_data["print_trees"],
        )



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
    conf = TestDPProofConf.from_yaml(yaml_conf)
    sentence_db = SentenceDB.load(conf.sentence_db_loc)

    _logger.info(f"Starting tactic client.")
    clean_tactic_confs: list[TacticGenConf] = []
    all_commands: list[StartModelCommand] = []
    next_num = 0
    for tactic_conf in conf.tactic_confs:
        clean_tactic_conf, n_commands, commands = tactic_gen_to_client_conf(
            tactic_conf, next_num
        )
        all_commands.extend(commands)
        clean_tactic_confs.append(clean_tactic_conf)
        next_num = n_commands

    procs = []
    if 0 < len(all_commands):
        clear_port_map()
        procs = start_servers(all_commands)
        port_map = wait_for_servers(next_num)
        for tactic_conf in clean_tactic_confs:
            tactic_conf_update_ips(tactic_conf, port_map)

    conf.tactic_confs = clean_tactic_confs

    _logger.info(f"Running proof.")
    try:
        result = run_proof(conf.to_run_conf())
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
