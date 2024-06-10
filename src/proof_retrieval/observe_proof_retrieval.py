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
from proof_retrieval.proof_retriever import TextProofRetrieverConf, TextProofRetriever

from util.constants import CLEAN_CONFIG


@dataclass
class ProofObserveConf:
    data_loc: Path
    file_loc: Path
    data_split_loc: Path
    sentence_db_loc: Path
    proof_name: str
    step_idx: int
    proof_conf: TextProofRetrieverConf
    print_num: int

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> ProofObserveConf:
        return cls(
            Path(yaml_data["data_loc"]),
            Path(yaml_data["test_file"]),
            Path(yaml_data["data_split_loc"]),
            Path(yaml_data["sentence_db_loc"]),
            yaml_data["theorem_name"],
            yaml_data["step_idx"],
            TextProofRetrieverConf.from_yaml(yaml_data["proof_ret"]),
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


def print_proofs(conf: ProofObserveConf):
    data_split = DataSplit.load(conf.data_split_loc)
    sentence_db = SentenceDB.load(conf.sentence_db_loc)
    file_info, _ = get_file_from_split(conf.data_loc, data_split, conf.file_loc)
    dp_obj = file_info.get_dp(conf.data_loc, sentence_db)
    proof = find_proof(dp_obj, conf.proof_name)
    step = proof.steps[conf.step_idx]
    proof_retriever = TextProofRetriever.from_conf(conf.proof_conf)
    print("Getting similar proofs: ")
    similar_proofs = proof_retriever.get_similar_proofs(step, proof, dp_obj)[
        : conf.print_num
    ]
    print("\n\n".join([p.proof_text_to_string() for p in similar_proofs]))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "conf_loc", help="Location of premise observation configuration file."
    )
    args = parser.parse_args(sys.argv[1:])

    conf_loc = Path(args.conf_loc)

    with conf_loc.open("r") as fin:
        yaml_conf = yaml.load(fin, Loader=yaml.Loader)

    proof_conf = ProofObserveConf.from_yaml(yaml_conf)

    print_proofs(proof_conf)
