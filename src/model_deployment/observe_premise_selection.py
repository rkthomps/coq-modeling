from __future__ import annotations
from typing import Any
import yaml
import sys, os
import argparse
import pickle
from pathlib import Path
from dataclasses import dataclass

from data_management.sentence_db import SentenceDB
from data_management.dataset_file import DatasetFile, Proof
from data_management.splits import DataSplit, FileInfo, Split
from model_deployment.rerank_client import (
    PremiseConf,
    premise_conf_from_yaml,
    premise_client_from_conf,
)

from util.constants import CLEAN_CONFIG


@dataclass
class PremiseObserveConf:
    data_loc: Path
    file_loc: Path
    data_split_loc: Path
    sentence_db_loc: Path
    proof_name: str
    step_idx: int
    premise_conf: PremiseConf
    print_num: int

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> PremiseObserveConf:
        return cls(
            Path(yaml_data["data_loc"]),
            Path(yaml_data["test_file"]),
            Path(yaml_data["data_split_loc"]),
            Path(yaml_data["sentence_db_loc"]),
            yaml_data["theorem_name"],
            yaml_data["step_idx"],
            premise_conf_from_yaml(yaml_data["premise"]),
            yaml_data["print_num"],
        )


def get_file_from_split(
    data_loc: Path,
    data_split: DataSplit,
    test_file: Path,
) -> tuple[FileInfo, Split]:
    for split in Split:
        for file_info in data_split.get_file_list(split):
            info_path = data_loc / Path(file_info.file)
            if info_path.resolve() == test_file.resolve():
                return file_info, split
    raise ValueError(f"Could not find data points file corresponding to {test_file}")


def find_proof(
    dp_obj: DatasetFile,
    proof_name: str,
) -> Proof:
    for proof in dp_obj.proofs:
        if proof.get_theorem_name() == proof_name:
            return proof
    raise ValueError(f"Could not find proof {proof_name}")


def print_premises(conf: PremiseObserveConf):
    data_split = DataSplit.load(conf.data_split_loc)
    sentence_db = SentenceDB.load(conf.sentence_db_loc)
    file_info, split = get_file_from_split(conf.data_loc, data_split, conf.file_loc)
    dp_obj = file_info.get_dp(conf.data_loc, sentence_db)
    proof = find_proof(dp_obj, conf.proof_name)
    step = proof.steps[conf.step_idx]
    premise_client = premise_client_from_conf(conf.premise_conf)
    filter_result = premise_client.premise_filter.get_pos_and_avail_premises(
        step, proof, dp_obj
    )
    ranked_premises = premise_client.get_ranked_premise_generator(
        step, proof, dp_obj, filter_result.avail_premises
    )
    print("Getting premises for proof: ")
    print(proof.proof_prefix_to_string(step))
    print("Next step: ")
    print(step.step.text)
    for i, prem in enumerate(ranked_premises):
        if conf.print_num <= i:
            break
        print(prem.text)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "conf_loc", help="Location of premise observation configuration file."
    )
    args = parser.parse_args(sys.argv[1:])

    with Path(CLEAN_CONFIG).open("rb") as fin:
        conf = pickle.load(fin)

    print_premises(conf)
