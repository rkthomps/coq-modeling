from __future__ import annotations

from typing import Any
import sys, os
import argparse
import pickle
from pathlib import Path
from dataclasses import dataclass

from data_management.splits import DataSplit, Split, FileInfo
from data_management.sentence_db import SentenceDB
from data_management.dataset_file import DatasetFile, Term

from model_deployment.fast_client import FastLspClient, ClientWrapper
from model_deployment.proof_manager import ProofInfo, ProofManager
from model_deployment.mcts_searcher import MCTSSuccess, MCTSFailure
from model_deployment.classical_searcher import ClassicalSuccess, ClassicalFailure
from model_deployment.searcher import (
    SearcherConf,
    SuccessfulSearch,
    FailedSearch,
    searcher_from_conf,
)
from model_deployment.tactic_gen_client import TacticGenClient

from util.util import get_fresh_path


@dataclass
class LocationInfo:
    data_loc: Path
    file_info: FileInfo
    split: Split
    dataset_file: DatasetFile
    dp_proof_idx: int
    sentence_db: SentenceDB
    data_split: DataSplit


@dataclass
class RunProofConf:
    location_info: LocationInfo
    search_conf: SearcherConf
    tactic_gen: TacticGenClient
    print_proofs: bool
    print_trees: bool


def normalize(s: str) -> str:
    return " ".join(s.split())


def get_proof_info(
    data_loc: Path,
    file_info: FileInfo,
    term: Term,
) -> ProofInfo:
    file_loc = (data_loc / file_info.file).resolve()
    workspace_loc = (data_loc / file_info.workspace).resolve()
    workspace_uri = f"file://{workspace_loc.resolve()}"
    client = FastLspClient(workspace_uri, timeout=60)
    fresh_file_loc = get_fresh_path(file_loc, file_loc.name)
    client_wrapper = ClientWrapper(client, f"file://{fresh_file_loc}")
    with file_loc.open("r") as fin:
        file_contents = fin.read()
    steps = client_wrapper.write_and_get_steps(file_contents)
    client.shutdown()
    client.exit()
    for i, step in enumerate(steps):
        if normalize(step.text) in normalize(term.term.text) or normalize(
            term.term.text
        ) in normalize(step.text):
            return ProofInfo(term, steps[: (i + 1)], i)
    raise ValueError(f"Could not find step defining theorem {term.term.text}")


def run_proof(conf: RunProofConf) -> SuccessfulSearch | FailedSearch:
    proof_info = get_proof_info(
        conf.location_info.data_loc,
        conf.location_info.file_info,
        conf.location_info.dataset_file.proofs[conf.location_info.dp_proof_idx].theorem,
    )
    with ProofManager(
        conf.location_info.dataset_file.file_context,
        proof_info,
        conf.location_info.file_info,
        conf.location_info.sentence_db,
        conf.location_info.split,
        conf.location_info.data_loc,
    ) as proof_manager:
        tree_manager = searcher_from_conf(
            conf.search_conf, conf.tactic_gen, proof_manager
        )
        result = tree_manager.search(
            print_proofs=conf.print_proofs, print_trees=conf.print_trees
        )
        return result


@dataclass
class MCTSSummary:
    file: Path
    theorem: str
    success: bool
    search_time: float | None
    model_time: float | None

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
        ]
        return headers, {
            "file": str(self.file),
            "theorem": self.theorem,
            "success": self.success,
            "search_time": self.search_time,
            "model_time": self.model_time,
        }

    def pretty_print(self):
        if self.search_time is None:
            nice_str = "{:20s}{:20s} FAILURE BY ERROR.".format(
                str(self.file), self.theorem
            )
        else:
            success_str = "SUCCESS" if self.success else "FAILURE"
            nice_str = "{:20s}{:20s}{:10s} after {:3.2f} seconds.".format(
                str(self.file), self.theorem, success_str, self.search_time
            )
        print(nice_str)

    def __lt__(self, other: MCTSSummary) -> bool:
        if self.file == other.file:
            return self.theorem < other.theorem
        return self.file < other.file

    @classmethod
    def from_search_result(
        cls, file: Path, theorem: str, result: MCTSSuccess | MCTSFailure | None
    ) -> MCTSSummary:
        match result:
            case MCTSSuccess():
                return cls(file, theorem, True, result.time, result.model_time)
            case MCTSFailure():
                return cls(file, theorem, False, result.time, result.model_time)
            case None:
                return cls(file, theorem, False, None, None)


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
        if self.search_time is None:
            nice_str = "{:20s}{:20s} FAILURE BY ERROR.".format(
                str(self.file), self.theorem
            )
        else:
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
        cls,
        file: Path,
        theorem: str,
        result: ClassicalSuccess | ClassicalFailure | None,
    ) -> SearchSummary:
        if result is None:
            return cls(file, theorem, False, None, None, None, None, None, None, None)
        search_size = result.search_tree.root.size()
        num_errors = result.search_tree.root.num_errors()
        num_pruned = result.search_tree.root.num_pruned()
        _, max_depth = result.search_tree.root.get_deepest_node()
        match result:
            case ClassicalSuccess():
                path_to_qed = result.search_tree.root.get_path_to_qed()
                assert 2 <= len(path_to_qed)
                assert path_to_qed[-2].expanded is not None
                expand_num = path_to_qed[-2].expanded
                search_time = result.total_search_time / 1e9
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
            case ClassicalFailure():
                expand_num = result.search_tree.root.get_last_node_expanded()
                search_time = result.total_search_time / 1e9
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


Summary = MCTSSummary | SearchSummary


def summary_from_result(
    file: Path,
    theorem: str,
    result: ClassicalSuccess | ClassicalFailure | MCTSSuccess | MCTSFailure,
) -> Summary:
    match result:
        case ClassicalSuccess() | ClassicalFailure():
            return SearchSummary.from_search_result(file, theorem, result)
        case MCTSSuccess() | MCTSFailure():
            return MCTSSummary.from_search_result(file, theorem, result)


if __name__ == "__main__":
    """This section of the file is just here for evaluation."""
    from evaluation.evaluate import EvalConf

    parser = argparse.ArgumentParser()
    parser.add_argument("eval_conf_loc")
    parser.add_argument("proof_map_loc")
    parser.add_argument("proof_map_idx", type=int)

    args = parser.parse_args(sys.argv[1:])
    eval_conf_loc = Path(args.eval_conf_loc)
    proof_map_loc = Path(args.proof_map_loc)
    proof_map_idx = args.proof_map_idx
    assert isinstance(proof_map_idx, int)

    eval_conf = EvalConf.from_yaml(eval_conf_loc)
