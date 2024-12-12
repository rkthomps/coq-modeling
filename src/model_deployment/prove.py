from __future__ import annotations

from typing import Any, Optional
import sys, os
import glob
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
from model_deployment.whole_proof_searcher import WholeProofSuccess, WholeProofFailure
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
from coqstoq.check import Result
from coqstoq.eval_thms import EvalTheorem


@dataclass
class LocationInfo:
    data_loc: Path
    file_loc: Path
    workspace_loc: Path
    dataset_file: DatasetFile
    dp_proof_idx: int
    sentence_db: SentenceDB


@dataclass
class RunProofConf:
    loc: LocationInfo
    search_conf: SearcherConf
    tactic_gens: list[TacticGenClient]
    print_proofs: bool
    print_trees: bool

    @property
    def theorem(self) -> str:
        return self.loc.dataset_file.proofs[self.loc.dp_proof_idx].theorem.term.text

    @property
    def module(self) -> list[str]:
        return self.loc.dataset_file.proofs[self.loc.dp_proof_idx].theorem.term.module

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
    file_loc: Path,
    workspace_loc: Path,
    term: Term,
) -> ProofInfo:
    workspace_uri = f"file://{workspace_loc.resolve()}"
    client = FastLspClient(workspace_uri, timeout=240)
    fresh_file_loc = get_fresh_path(file_loc, file_loc.name)
    client_wrapper = ClientWrapper(client, f"file://{fresh_file_loc}")
    with file_loc.open("r") as fin:
        file_contents = fin.read()
    steps = client_wrapper.write_and_get_steps(file_contents)
    client.shutdown()
    client.exit()
    for i, step in enumerate(steps):
        if normalize(term.term.text) in normalize(step.text):
            if step.ast.range.start.line == term.term.line:
                return ProofInfo(term, steps[: (i + 1)], i)
    raise ValueError(f"Could not find step defining theorem {term.term.text}")


def run_proof(conf: RunProofConf) -> SuccessfulSearch | FailedSearch:
    for f in glob.glob(".*.cache"):
        os.remove(f)
    target_theorem = conf.loc.dataset_file.proofs[conf.loc.dp_proof_idx].theorem
    occurance = 0
    for proof in conf.loc.dataset_file.proofs[: conf.loc.dp_proof_idx]:
        if normalize(target_theorem.term.text) == normalize(proof.theorem.term.text):
            occurance += 1
    proof_info = get_proof_info(
        conf.loc.data_loc,
        conf.loc.file_loc,
        conf.loc.workspace_loc,
        conf.loc.dataset_file.proofs[conf.loc.dp_proof_idx].theorem,
    )
    for tgen in conf.tactic_gens:
        tgen.set_seed(0)
    with ProofManager(
        conf.loc.dataset_file.file_context,
        conf.loc.dataset_file.proofs[: conf.loc.dp_proof_idx],
        proof_info,
        conf.loc.file_loc,
        conf.loc.workspace_loc,
        conf.loc.sentence_db,
        conf.loc.data_loc,
    ) as proof_manager:
        tree_manager = searcher_from_conf(
            conf.search_conf, conf.tactic_gens, proof_manager
        )
        result = tree_manager.search(
            print_proofs=conf.print_proofs, print_trees=conf.print_trees
        )
        return result


def get_save_loc(save_dir: Path, thm: EvalTheorem) -> Path:
    return (
        save_dir
        / thm.project.workspace.name
        / thm.path
        / f"{thm.theorem_start_pos.line}-{thm.theorem_start_pos.column}.json"
    )


class RangoResult(Result):
    def __init__(
        self,
        thm: EvalTheorem,
        proof: Optional[str],
        time: Optional[float],
        n_attempts: Optional[int],
    ) -> None:
        super().__init__(thm, proof, time)
        self.n_attempts = n_attempts

    def to_json(self) -> Any:
        parent_json = super().to_json()
        return parent_json | {"n_attempts": self.n_attempts}

    def save(self, path: Path):
        os.makedirs(path.parent, exist_ok=True)
        with path.open("w") as fout:
            fout.write(json.dumps(self.to_json(), indent=2))

    @classmethod
    def from_json(cls, json_data: Any) -> RangoResult:
        return cls(
            EvalTheorem.from_json(json_data["thm"]),
            json_data["proof"],
            json_data["time"],
            json_data["n_attempts"],
        )

    @classmethod
    def from_search_result(cls, thm: EvalTheorem, result: SearchResult) -> RangoResult:
        match result:
            case ClassicalSuccess():
                return cls(
                    thm,
                    result.successful_candidate.proof_str,
                    result.time,
                    result.search_steps,
                )
            case ClassicalFailure():
                return cls(thm, None, result.time, result.search_steps)
            case StraightLineSuccess():
                return cls(
                    thm,
                    result.successful_proof.proof_text_to_string(include_theorem=False),
                    result.time,
                    len(result.attempted_proofs),
                )
            case StraightLineFailure():
                return cls(thm, None, result.time, len(result.attempted_proofs))
            case WholeProofSuccess():
                return cls(
                    thm,
                    result.successful_proof.proof_text_to_string(include_theorem=False),
                    result.time,
                    len(result.attempted_proofs),
                )
            case WholeProofFailure():
                return cls(thm, None, result.time, len(result.attempted_proofs))


def load_result(file: Path) -> RangoResult:
    with file.open("r") as fin:
        json_data = json.load(fin)
    return RangoResult.from_json(json_data)


def load_results(save_dir: Path) -> list[RangoResult]:
    results: list[RangoResult] = []
    for f in os.listdir(save_dir):
        if not f.endswith(".json"):
            continue
        result = load_result(save_dir / f)
        results.append(result)
    return results
