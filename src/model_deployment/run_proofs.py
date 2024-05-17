from __future__ import annotations
import os
import sys
import csv
import ipdb
from typing import Any
from pathlib import Path
from dataclasses import dataclass
from threading import Thread
import multiprocessing as mp
from multiprocessing import context
from multiprocessing.pool import AsyncResult
import pickle

from model_deployment.run_proof import (
    run_proof,
    TestProofConf,
    TheoremLocationInfo,
)

from model_deployment.prove import RunProofConf, LocationInfo, Summary, run_proof, summary_from_result

from model_deployment.searcher import (
    SearcherConf,
    searcher_conf_from_yaml,
)
from model_deployment.tactic_gen_client import TacticGenConf, tactic_gen_conf_from_yaml
from util.constants import CLEAN_CONFIG
from util.util import get_basic_logger

_logger = get_basic_logger(__name__)


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
    save_loc: Path
    data_loc: Path
    sentence_db_loc: Path
    data_split_loc: Path
    search_conf: SearcherConf
    tactic_conf: TacticGenConf

    def to_test_proof_list(self) -> list[TestProofConf]:
        test_proof_confs: list[TestProofConf] = []
        for p in self.proofs:
            location = TheoremLocationInfo(
                p.theorem_name,
                p.test_file,
                self.data_loc,
                self.sentence_db_loc,
                self.data_split_loc,
            )
            test_proof_conf = TestProofConf(
                location,
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
            Path(yaml_data["save_loc"]),
            Path(yaml_data["data_loc"]),
            Path(yaml_data["sentence_db_loc"]),
            Path(yaml_data["data_split_loc"]),
            searcher_conf_from_yaml(yaml_data["search"]),
            tactic_gen_conf_from_yaml(yaml_data["tactic_gen"]),
        )



def run_test(test_proof: TestProofConf, save_dir: Path):
    run_conf = test_proof.to_run_conf()
    result = run_proof(run_conf)
    file = test_proof.theorem_location_info.test_file.relative_to(
        test_proof.theorem_location_info.data_loc
    )
    theorem = test_proof.theorem_location_info.theorem_name
    summary = summary_from_result(file, theorem, result)
    summary.pretty_print()
    summary.save(save_dir)


def load_results(save_dir: Path) -> list[Summary]:
    summaries: list[Summary] = []
    for f in os.listdir(save_dir):
        if not f.endswith(".pkl"):
            continue
        with (save_dir / f).open("rb") as fin:
            summary = pickle.load(fin)
            summaries.append(summary)
    return summaries


if __name__ == "__main__":
    conf_loc = Path(f"./{CLEAN_CONFIG}")
    with conf_loc.open("rb") as fin:
        conf: TestProofsConf = pickle.load(fin)
        assert "TestProofsConf" in str(conf.__class__)  # isinstance didn't work

    assert not conf.save_loc.exists()
    os.makedirs(conf.save_loc)

    test_proof_confs = conf.to_test_proof_list()
    process_results: list[AsyncResult] = []
    with mp.Pool(conf.n_procs) as pool:
        for t in test_proof_confs:
            res = pool.apply_async(run_test, (t, conf.save_loc))
            process_results.append(res)

        for r in process_results:
            r.get(2 * conf.search_conf.timeout)
            # except Exception as e:
            #     _logger.warning(f"Got exception: {e}")

    results = load_results(conf.save_loc)
    results.sort()
    if 0 == len(results):
        print("Nothing to write.", file=sys.stderr)

    with (conf.save_loc / "results.csv").open("w", newline="") as fout:
        field_names, _ = results[0].to_csv_dict()
        writer = csv.DictWriter(fout, field_names)
        writer.writeheader()
        for r in results:
            _, r_dict = r.to_csv_dict()
            writer.writerow(r_dict)
