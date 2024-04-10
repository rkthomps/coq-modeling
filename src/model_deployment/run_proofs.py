from __future__ import annotations
from typing import Any
from pathlib import Path
from dataclasses import dataclass
import multiprocessing as mp
import pickle

from model_deployment.run_proof import run_proof, TestProofConf
from model_deployment.searcher import SearchConf, SuccessfulSearch, FailedSearch
from model_deployment.tactic_gen_client import TacticGenConf, tactic_gen_conf_from_yaml
from util.constants import CLEAN_CONFIG


@dataclass
class ProofConf:
    test_file: Path
    theorem_name: str

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> ProofConf:
        return cls(Path(yaml_data["test_file"]), yaml_data["theorem_name"])


@dataclass
class TestProofsConf:
    proofs: list[ProofConf]
    n_procs: int
    data_loc: Path
    sentence_db_loc: Path
    data_split_loc: Path
    search_conf: SearchConf
    tactic_conf: TacticGenConf

    def to_test_proof_list(self) -> list[TestProofConf]:
        test_proof_confs: list[TestProofConf] = []
        for p in self.proofs:
            test_proof_conf = TestProofConf(
                p.theorem_name,
                p.test_file,
                self.data_loc,
                self.sentence_db_loc,
                self.data_split_loc,
                self.search_conf,
                self.tactic_conf,
                False,
                False,
            )
            test_proof_confs.append(test_proof_conf)
        return test_proof_confs

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> TestProofsConf:
        return cls(
            [ProofConf.from_yaml(p) for p in yaml_data["proofs"]],
            yaml_data["n_procs"],
            Path(yaml_data["data_loc"]),
            Path(yaml_data["sentence_db_loc"]),
            Path(yaml_data["data_split_loc"]),
            SearchConf.from_yaml(yaml_data["search"]),
            tactic_gen_conf_from_yaml(yaml_data["tactic_gen"]),
        )


def run_test(test_proof: TestProofConf) -> None:
    result = run_proof(test_proof.to_run_conf())
    match result:
        case SuccessfulSearch():
            print(
                "{:50}{:30}......SUCCESS".format(
                    test_proof.test_file, test_proof.theorem_name
                )
            )
        case FailedSearch():
            print(
                "{:50}{:30}......FAILURE".format(
                    test_proof.test_file, test_proof.theorem_name
                )
            )


if __name__ == "__main__":
    conf_loc = Path(f"./{CLEAN_CONFIG}")
    with conf_loc.open("rb") as fin:
        conf: TestProofsConf = pickle.load(fin)
        assert "TestProofsConf" in str(conf.__class__)  # isinstance didn't work

    test_proof_confs = conf.to_test_proof_list()
    with mp.Pool(conf.n_procs) as pool:
        pool.map(run_test, test_proof_confs)
