from __future__ import annotations
from typing import Any
from pathlib import Path
import pickle
import os, sys
import csv
import json
import time

from dataclasses import dataclass
from tactic_gen.lm_example import LmExample
from model_deployment.proof_manager import ProofManager
from model_deployment.whole_proof_searcher import WholeProofSearcher, WholeProofResult
from model_deployment.run_proof import LocationInfo, TheoremLocationInfo, get_proof_info
from model_deployment.run_whole_proof import TestWholeProofConf, RunWholeProofConf
from model_deployment.run_proofs import ProofConf
from model_deployment.tactic_gen_client import (
    TacticGenClient,
    TacticGenConf,
    tactic_gen_conf_from_yaml,
    tactic_gen_client_from_conf,
)

from util.constants import CLEAN_CONFIG


@dataclass
class TestWholeProofsConf:
    proofs: list[ProofConf]
    n_procs: int
    save_loc: Path
    data_loc: Path
    sentence_db_loc: Path
    data_split_loc: Path
    tactic_conf: TacticGenConf
    n_attempts: int

    def to_test_proof_list(self) -> list[TestWholeProofConf]:
        test_proof_confs: list[TestWholeProofConf] = []
        for p in self.proofs:
            location = TheoremLocationInfo(
                p.theorem_name,
                p.test_file,
                self.data_loc,
                self.sentence_db_loc,
                self.data_split_loc,
            )
            test_proof_conf = TestWholeProofConf(
                location, self.tactic_conf, self.n_attempts
            )
            test_proof_confs.append(test_proof_conf)
        return test_proof_confs

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> TestWholeProofsConf:
        return cls(
            [ProofConf.from_yaml(p) for p in yaml_data["proofs"]],
            yaml_data["n_procs"],
            Path(yaml_data["save_loc"]),
            Path(yaml_data["data_loc"]),
            Path(yaml_data["sentence_db_loc"]),
            Path(yaml_data["data_split_loc"]),
            tactic_gen_conf_from_yaml(yaml_data["tactic_gen"]),
            yaml_data["n_attempts"],
        )


@dataclass
class WholeProofSummary:
    file: Path
    theorem: str
    prompt: LmExample
    successes: list[str]
    failures: list[str]
    total_time: float

    def __lt__(self, other: WholeProofSummary) -> bool:
        return self.file < other.file

    def to_json(self) -> Any:
        return {
            "file": str(self.file),
            "theorem": self.theorem,
            "prompt": self.prompt.to_json(),
            "successes": self.successes,
            "failures": self.failures,
            "total_time": self.total_time,
        }

    def to_csv_dict(self) -> tuple[list[str], dict[str, Any]]:
        headers = [
            "file",
            "theorem",
            "successes",
            "failures",
            "total_time",
        ]
        return headers, {
            "file": str(self.file),
            "theorem": self.theorem,
            "successes": len(self.successes),
            "failures": len(self.failures),
            "total_time": self.total_time,
        }

    @classmethod
    def load(cls, path: Path | str) -> WholeProofSummary:
        with open(path, "r") as fin:
            data = json.load(fin)
        return cls.from_json(data)

    @classmethod
    def from_json(cls, json_data: Any) -> WholeProofSummary:
        return cls(
            Path(json_data["file"]),
            json_data["theorem"],
            LmExample.from_json(json_data["prompt"]),
            json_data["successes"],
            json_data["failures"],
            json_data["total_time"],
        )

    @classmethod
    def from_whole_proof_result(
        cls, result: WholeProofResult, file: Path, theorem: str
    ) -> WholeProofSummary:
        return cls(
            file,
            theorem,
            result.prompt_example,
            result.successes,
            result.failures,
            result.time,
        )


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
        conf: TestWholeProofsConf = pickle.load(fin)
        assert "TestWholeProofsConf" in str(conf.__class__)  # isinstance didn't work
        if conf.save_loc.exists():
            raise FileExistsError(conf.save_loc)
        os.makedirs(conf.save_loc)

        test_whole_proof_confs = conf.to_test_proof_list()
        results: list[WholeProofSummary] = []
        for c in test_whole_proof_confs:
            result = run_proof(c.to_run_conf())
            summary = WholeProofSummary.from_whole_proof_result(
                result,
                c.theorem_location_info.test_file,
                c.theorem_location_info.theorem_name,
            )
            save_name = str(
                c.theorem_location_info.test_file / c.theorem_location_info.theorem_name
            ).replace(os.path.sep, "-")
            save_loc = conf.save_loc / save_name
            with save_loc.open("w") as fout:
                fout.write(json.dumps(summary.to_json(), indent=2))
            results.append(summary)

        results.sort()
        if 0 == len(results):
            print("Nothing to write", file=sys.stderr)
        summary_loc = conf.save_loc / "summary.csv"
        with summary_loc.open("w") as fout:
            field_names, _ = results[0].to_csv_dict()
            writer = csv.DictWriter(fout, field_names)
            writer.writeheader()
            for r in results:
                _, r_dict = r.to_csv_dict()
                writer.writerow(r_dict)
