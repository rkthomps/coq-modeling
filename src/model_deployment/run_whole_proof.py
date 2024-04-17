from __future__ import annotations
from typing import Any
from pathlib import Path
import pickle

from dataclasses import dataclass
from model_deployment.proof_manager import ProofManager
from model_deployment.whole_proof_searcher import WholeProofSearcher, WholeProofResult
from model_deployment.run_proof import LocationInfo, TheoremLocationInfo, get_proof_info
from model_deployment.tactic_gen_client import (
    TacticGenClient,
    TacticGenConf,
    tactic_gen_conf_from_yaml,
    tactic_gen_client_from_conf,
)

from util.constants import CLEAN_CONFIG


@dataclass
class TestWholeProofConf:
    theorem_location_info: TheoremLocationInfo
    tactic_conf: TacticGenConf
    n_attempts: int

    def to_run_conf(self) -> RunWholeProofConf:
        return RunWholeProofConf(
            self.theorem_location_info.to_location_info(),
            tactic_gen_client_from_conf(self.tactic_conf),
            self.n_attempts,
        )

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> TestWholeProofConf:
        return cls(
            TheoremLocationInfo.from_yaml(yaml_data["thm_info"]),
            tactic_gen_conf_from_yaml(yaml_data["tactic_gen"]),
            yaml_data["n_attempts"],
        )


@dataclass
class RunWholeProofConf:
    location_info: LocationInfo
    tactic_gen: TacticGenClient
    n_attempts: int


def run_proof(conf: RunWholeProofConf) -> WholeProofResult:
    proof_info = get_proof_info(
        conf.location_info.data_loc,
        conf.location_info.file_info,
        conf.location_info.dataset_file.proofs[conf.location_info.dp_proof_idx].theorem,
    )
    with ProofManager(
        conf.location_info.dataset_file.file_context,
        proof_info,
        conf.tactic_gen.formatter,
        conf.location_info.file_info,
        conf.location_info.sentence_db,
        conf.location_info.split,
        conf.location_info.data_loc,
    ) as proof_manager:
        searcher = WholeProofSearcher(conf.tactic_gen, proof_manager, conf.n_attempts)
        result = searcher.search()
        return result


if __name__ == "__main__":
    conf_loc = Path(f"./{CLEAN_CONFIG}")
    with conf_loc.open("rb") as fin:
        conf: TestWholeProofConf = pickle.load(fin)
        assert "TestWholeProofConf" in str(conf.__class__)  # isinstance didn't work
        result = run_proof(conf.to_run_conf())
        print("Successful attempts:")
        for s in result.successes:
            print(s)

        print()
        print("Failed attempts:")
        for s in result.failures:
            print(s)
