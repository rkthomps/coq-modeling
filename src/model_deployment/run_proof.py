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


@dataclass
class TestProofConf:
    thm: EvalTheorem
    coqstoq_loc: Path
    data_loc: Path
    sentence_db_loc: Path
    search_conf: SearcherConf
    tactic_confs: list[TacticGenConf]
    print_proofs: bool
    print_trees: bool

    def update_ips(self, port_map: dict[int, tuple[str, int]]):
        for conf in self.tactic_confs:
            tactic_conf_update_ips(conf, port_map)

    def to_run_conf(self) -> RunProofConf:
        sentence_db = SentenceDB.load(self.sentence_db_loc)
        thm_desc = get_thm_desc(self.thm, self.data_loc, sentence_db)
        assert thm_desc is not None

        location_info = LocationInfo(
            self.data_loc,
            get_file_loc(self.thm, self.coqstoq_loc),
            get_workspace_loc(self.thm, self.coqstoq_loc),
            thm_desc.dp,
            thm_desc.idx,
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
    def from_yaml(cls, yaml_data: Any) -> TestProofConf:
        split = str2split(yaml_data["split"])
        coqstoq_loc = Path(yaml_data["coqstoq_loc"])
        theorem = get_theorem(split, yaml_data["thm_idx"], coqstoq_loc)
        if "tactic_gen" in yaml_data:
            tactic_gen_confs = [tactic_gen_conf_from_yaml(yaml_data["tactic_gen"])]
        elif "tactic_gens" in yaml_data:
            tactic_gen_confs = [
                tactic_gen_conf_from_yaml(conf) for conf in yaml_data["tactic_gens"]
            ]
        else:
            raise ValueError("No tactic_gen or tactic_gens in yaml_data.")
        return cls(
            theorem,
            coqstoq_loc,
            Path(yaml_data["data_loc"]),
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
    conf = TestProofConf.from_yaml(yaml_conf)
    sentence_db = SentenceDB.load(conf.sentence_db_loc)
    thm_desc = get_thm_desc(conf.thm, conf.data_loc, sentence_db)
    assert thm_desc is not None

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
