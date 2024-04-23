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
    RunProofConf,
)
from model_deployment.searcher import SearchConf, SuccessfulSearch, FailedSearch
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
    search_conf: SearchConf
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
            SearchConf.from_yaml(yaml_data["search"]),
            tactic_gen_conf_from_yaml(yaml_data["tactic_gen"]),
        )


@dataclass
class SearchSummary:
    file: Path
    theorem: str
    success: bool
    search_steps: int | None
    max_depth: int | None
    num_proofs_attempted: int | None
    search_time: float | None
    model_time: float | None
    num_tactic_errors: int | None
    num_nodes_pruned: int | None

    def save(self, save_dir: Path) -> None:
        save_loc = save_dir / str(self.file / self.theorem).replace(os.path.sep, "-")
        with save_loc.open("wb") as fout:
            fout.write(pickle.dumps(self))

    def to_csv_dict(self) -> tuple[list[str], dict[str, Any]]:
        headers = [
            "file",
            "theorem",
            "success",
            "search_time",
            "model_time",
            "search_steps",
            "max_depth",
            "num_proofs_attempted",
            "num_tactic_errors",
            "num_nodes_pruned",
        ]
        return headers, {
            "file": str(self.file),
            "theorem": self.theorem,
            "success": self.success,
            "search_steps": self.search_steps,
            "max_depth": self.max_depth,
            "num_proofs_attempted": self.num_proofs_attempted,
            "search_time": self.search_time,
            "model_time": self.model_time,
            "num_tactic_errors": self.num_tactic_errors,
            "num_nodes_pruned": self.num_nodes_pruned,
        }

    def pretty_print(self):
        success_str = "SUCCESS" if self.success else "FAILURE"
        nice_str = "{:20s}{:20s}{:10s} after {:3.2f} seconds.".format(
            str(self.file), self.theorem, success_str, self.search_time
        )
        print(nice_str)

    def __lt__(self, other: SearchSummary) -> bool:
        if self.file == other.file:
            return self.theorem < other.theorem
        return self.file < other.file

    @classmethod
    def from_search_result(
        cls, file: Path, theorem: str, result: SuccessfulSearch | FailedSearch | None
    ) -> SearchSummary:
        if result is None:
            return cls(file, theorem, False, None, None, None, None, None, None, None)
        search_size = result.search_tree.root.size()
        num_errors = result.search_tree.root.num_errors()
        num_pruned = result.search_tree.root.num_pruned()
        _, max_depth = result.search_tree.root.get_deepest_node()
        match result:
            case SuccessfulSearch():
                path_to_qed = result.search_tree.root.get_path_to_qed()
                assert 2 <= len(path_to_qed)
                assert path_to_qed[-2].expanded is not None
                expand_num = path_to_qed[-2].expanded
                search_time = result.qed_node.creation_time / 1e9
                return SearchSummary(
                    file,
                    theorem,
                    True,
                    expand_num,
                    max_depth,
                    search_size,
                    search_time,
                    result.total_model_time,
                    num_errors,
                    num_pruned,
                )
            case FailedSearch():
                expand_num = result.search_tree.root.get_last_node_expanded()
                search_time = result.search_tree.root.get_last_node_time() / 1e9
                return SearchSummary(
                    file,
                    theorem,
                    False,
                    expand_num,
                    max_depth,
                    search_size,
                    search_time,
                    result.total_model_time,
                    num_errors,
                    num_pruned,
                )


def run_test(test_proof: TestProofConf, save_dir: Path):
    run_conf = test_proof.to_run_conf()
    result = run_proof(run_conf)
    summary = SearchSummary.from_search_result(
        test_proof.theorem_location_info.test_file.relative_to(
            test_proof.theorem_location_info.data_loc
        ),
        test_proof.theorem_location_info.theorem_name,
        result,
    )
    summary.pretty_print()
    summary.save(save_dir)


def load_results(save_dir: Path) -> list[SearchSummary]:
    summaries: list[SearchSummary] = []
    for f in os.listdir(save_dir):
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
            r.get(1.1 * conf.search_conf.timeout)
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
