from __future__ import annotations

from typing import Any, Optional
import sys, os
import argparse
import pickle
import json
from pathlib import Path
from dataclasses import dataclass

from data_management.splits import DataSplit, Split, FileInfo
from data_management.sentence_db import SentenceDB
from data_management.dataset_file import DatasetFile, Term

from model_deployment.fast_client import FastLspClient, ClientWrapper
from model_deployment.proof_manager import ProofInfo, ProofManager
from model_deployment.straight_line_searcher import (
    StraightLineSuccess,
    StraightLineFailure,
)
from model_deployment.classical_searcher import ClassicalSuccess, ClassicalFailure
from model_deployment.searcher import (
    SearcherConf,
    SuccessfulSearch,
    FailedSearch,
    SearchResult,
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
    loc: LocationInfo
    search_conf: SearcherConf
    tactic_gen: TacticGenClient
    print_proofs: bool
    print_trees: bool

    @property
    def file(self) -> Path:
        return self.loc.data_loc / self.loc.file_info.file

    @property
    def theorem(self) -> str:
        return self.loc.dataset_file.proofs[self.loc.dp_proof_idx].theorem.term.text

    @property
    def theorem_id(self) -> str:
        theorem_name = self.loc.dataset_file.proofs[
            self.loc.dp_proof_idx
        ].get_theorem_name()
        return theorem_name + "-" + str(self.loc.dp_proof_idx)


def normalize(s: str) -> str:
    return " ".join(s.split())


def get_proof_info(
    data_loc: Path,
    file_info: FileInfo,
    term: Term,
    occurance: int,
) -> ProofInfo:
    file_loc = (data_loc / file_info.file).resolve()
    workspace_loc = (data_loc / file_info.workspace).resolve()
    workspace_uri = f"file://{workspace_loc.resolve()}"
    client = FastLspClient(workspace_uri, timeout=240)
    fresh_file_loc = get_fresh_path(file_loc, file_loc.name)
    client_wrapper = ClientWrapper(client, f"file://{fresh_file_loc}")
    with file_loc.open("r") as fin:
        file_contents = fin.read()
    steps = client_wrapper.write_and_get_steps(file_contents)
    client.shutdown()
    client.exit()
    num_seen = 0
    for i, step in enumerate(steps):
        if normalize(term.term.text) in normalize(step.text):
            if num_seen == occurance:
                return ProofInfo(term, steps[: (i + 1)], i)
            num_seen += 1
    raise ValueError(f"Could not find step defining theorem {term.term.text}")


def run_proof(conf: RunProofConf) -> SuccessfulSearch | FailedSearch:
    target_theorem = conf.loc.dataset_file.proofs[conf.loc.dp_proof_idx].theorem
    occurance = 0
    for proof in conf.loc.dataset_file.proofs[: conf.loc.dp_proof_idx]:
        if normalize(target_theorem.term.text) == normalize(proof.theorem.term.text):
            occurance += 1
    proof_info = get_proof_info(
        conf.loc.data_loc,
        conf.loc.file_info,
        conf.loc.dataset_file.proofs[conf.loc.dp_proof_idx].theorem,
        occurance,
    )
    with ProofManager(
        conf.loc.dataset_file.file_context,
        conf.loc.dataset_file.proofs[: conf.loc.dp_proof_idx],
        proof_info,
        conf.loc.file_info,
        conf.loc.sentence_db,
        conf.loc.split,
        conf.loc.data_loc,
    ) as proof_manager:
        tree_manager = searcher_from_conf(
            conf.search_conf, conf.tactic_gen, proof_manager
        )
        result = tree_manager.search(
            print_proofs=conf.print_proofs, print_trees=conf.print_trees
        )
        return result


@dataclass
class ClassicalSummary:
    file: Path
    theorem: str
    proof_idx: int
    theorem_id: str
    success: bool
    proof: Optional[str]
    search_steps: int | None
    search_time: float | None
    model_time: float | None

    ALIAS = "classical"

    def print_detailed_summary(self):
        print("File:", self.file)
        print("Theorem:", self.theorem)
        print("Success:", self.success)
        if self.success:
            assert self.proof is not None
            print("Proof:", self.proof)

    def to_json(self) -> Any:
        return {
            "file": str(self.file),
            "theorem": self.theorem,
            "proof_idx": self.proof_idx,
            "theorem_id": self.theorem_id,
            "success": self.success,
            "proof": self.proof,
            "search_steps": self.search_steps,
            "search_time": self.search_time,
            "model_time": self.model_time,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> ClassicalSummary:
        return cls(
            Path(json_data["file"]),
            json_data["theorem"],
            json_data["proof_idx"],
            json_data["theorem_id"],
            json_data["success"],
            json_data["proof"],
            json_data["search_steps"],
            json_data["search_time"],
            json_data["model_time"],
        )

    def to_csv_dict(self) -> tuple[list[str], dict[str, Any]]:
        headers = [
            "file",
            "theorem",
            "success",
            "search_steps",
            "search_time",
            "model_time",
        ]
        return headers, {
            "file": str(self.file),
            "theorem": self.theorem,
            "success": self.success,
            "search_steps": self.search_steps,
            "search_time": self.search_time,
            "model_time": self.model_time,
        }

    def __lt__(self, other: ClassicalSummary) -> bool:
        if self.file == other.file:
            return self.theorem < other.theorem
        return self.file < other.file

    @classmethod
    def from_search_result(
        cls,
        file: Path,
        theorem: str,
        proof_idx: int,
        theorem_id: str,
        result: ClassicalSuccess | ClassicalFailure | None,
    ) -> ClassicalSummary:
        if result is None:
            return cls(
                file,
                theorem,
                proof_idx,
                theorem_id,
                False,
                None,
                None,
                None,
                None,
            )
        match result:
            case ClassicalSuccess():
                return ClassicalSummary(
                    file,
                    theorem,
                    proof_idx,
                    theorem_id,
                    True,
                    result.successful_candidate.proof_str,
                    result.search_steps,
                    result.time,
                    result.model_time,
                )
            case ClassicalFailure():
                return ClassicalSummary(
                    file,
                    theorem,
                    proof_idx,
                    theorem_id,
                    False,
                    None,
                    result.search_steps,
                    result.time,
                    result.model_time,
                )


@dataclass
class StraightLineSummary:
    file: Path
    theorem: str
    proof_idx: int
    theorem_id: str
    success: bool
    proof: str | None
    attempts: list[str] | None
    search_time: float | None
    model_time: float | None

    ALIAS = "straight"

    def __lt__(self, other: ClassicalSummary) -> bool:
        if self.file == other.file:
            return self.theorem < other.theorem
        return self.file < other.file

    def print_detailed_summary(self):
        print("File:", self.file)
        print("Theorem:", self.theorem)
        print("Success:", self.success)
        if self.success:
            assert self.proof is not None
            print("Proof:", self.proof)

        if self.attempts is not None:
            print("ATTEMPTS:")
            for attempt in self.attempts:
                print(attempt)
        else:
            print("No Attempts")

    def to_json(self) -> Any:
        return {
            "file": str(self.file),
            "theorem": self.theorem,
            "proof_idx": self.proof_idx,
            "theorem_id": self.theorem_id,
            "success": self.success,
            "proof": self.proof,
            "attempts": self.attempts,
            "search_time": self.search_time,
            "model_time": self.model_time,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> StraightLineSummary:
        return cls(
            Path(json_data["file"]),
            json_data["theorem"],
            json_data["proof_idx"],
            json_data["theorem_id"],
            json_data["success"],
            json_data["proof"],
            json_data["attempts"],
            json_data["search_time"],
            json_data["model_time"],
        )

    def to_csv_dict(self) -> tuple[list[str], dict[str, Any]]:
        headers = [
            "file",
            "theorem",
            "success",
            "search_time",
            "model_time",
            "num_attempts",
        ]
        return headers, {
            "file": str(self.file),
            "theorem": self.theorem,
            "success": self.success,
            "search_time": self.search_time,
            "model_time": self.model_time,
            "num_attempts": None if self.attempts is None else len(self.attempts),
        }

    @classmethod
    def from_search_result(
        cls,
        file: Path,
        theorem: str,
        proof_idx: int,
        theorem_id: str,
        search_result: StraightLineSuccess | StraightLineFailure | None,
    ):
        if search_result is None:
            return cls(
                file, theorem, proof_idx, theorem_id, False, None, None, None, None
            )
        match search_result:
            case StraightLineSuccess():
                proof_text = search_result.successful_proof.proof_text_to_string()
                return cls(
                    file,
                    theorem,
                    proof_idx,
                    theorem_id,
                    True,
                    proof_text,
                    search_result.attempted_proofs,
                    search_result.time,
                    search_result.model_time,
                )
            case StraightLineFailure():
                return cls(
                    file,
                    theorem,
                    proof_idx,
                    theorem_id,
                    False,
                    None,
                    search_result.attempted_proofs,
                    search_result.time,
                    search_result.model_time,
                )


def summary_from_json(json_data: Any) -> Summary:
    attempted_alias = json_data["alias"]
    match attempted_alias:
        case ClassicalSummary.ALIAS:
            return ClassicalSummary.from_json(json_data)
        case StraightLineSummary.ALIAS:
            return StraightLineSummary.from_json(json_data)
        case _:
            raise ValueError(f"Unknown alias {attempted_alias}")


def summary_to_json(summary: Summary) -> Any:
    return summary.to_json() | {"alias": summary.ALIAS}


def get_save_loc(summary: Summary, save_dir: Path):
    save_name = str(summary.file / (summary.theorem_id + ".json")).replace(
        os.path.sep, "-"
    )[-255:]
    return save_dir / save_name


def save_summary(summary: Summary, save_dir: Path):
    save_loc = get_save_loc(summary, save_dir)
    with save_loc.open("w") as fout:
        summary_json = summary_to_json(summary)
        fout.write(json.dumps(summary_json, indent=2))


def pretty_print_summary(summary: Summary):
    if summary.search_time is None:
        nice_str = "{:20s}{:20s} FAILURE BY ERROR.".format(
            str(summary.file), summary.theorem
        )
    else:
        success_str = "SUCCESS" if summary.success else "FAILURE"
        nice_str = "{:20s}{:20s}{:10s} after {:3.2f} seconds.".format(
            str(summary.file), summary.theorem, success_str, summary.search_time
        )
    print(nice_str)


Summary = ClassicalSummary | StraightLineSummary


def summary_from_result(
    file: Path,
    theorem: str,
    proof_idx: int,
    theorem_id: str,
    result: SearchResult,
) -> Summary:
    match result:
        case ClassicalSuccess() | ClassicalFailure():
            return ClassicalSummary.from_search_result(
                file, theorem, proof_idx, theorem_id, result
            )
        case StraightLineSuccess() | StraightLineFailure():
            return StraightLineSummary.from_search_result(
                file, theorem, proof_idx, theorem_id, result
            )
