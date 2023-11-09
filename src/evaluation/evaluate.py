from __future__ import annotations
from typing import Any, Iterable, Generator, Optional
from dataclasses import dataclass
import json
import sys, os
import re
import argparse
import random
import shutil
import time
import traceback
from threading import Thread
from enum import Enum


from coqpyt.coq.base_file import CoqFile
from coqpyt.coq.proof_file import ProofFile

from tactic_gen.lm_example import LmExample, LMEXAMPLE_ALIASES
from tactic_gen.step_parser import lex, IdTok
from data_management.split_raw_data import SPLITS, assignment_shape_expected
from data_management.create_lm_dataset import LmExampleConfig
from model_deployment.search_tree import ProofSearchTree
from model_deployment.searcher import SearchTreeManager, SearchResult
from model_deployment.proof_manager import (
    ProofManager,
    SEARCH_TOKEN,
    get_fresh_path,
    ProofCheckResult,
    TacticResult,
)
from model_deployment.model_wrapper import ModelWrapper, MODEL_WRAPPER_ALIASES
from model_deployment.node_score import NodeScore, NODE_SCORE_ALIASES
from evaluation.impose_file_hierarchy import (
    mapping_shape_correct,
    FILE_MAPPING_NAME,
    DESIRED_PREFIX,
)

from tqdm import tqdm
from yaml import load, Loader


class EvalSearchResult:
    def __init__(
        self,
        search_result: SearchResult,
        orig_file_path: str,
        thm_name: str,
        thm_idx: int,
    ) -> None:
        assert isinstance(search_result, SearchResult)
        assert isinstance(orig_file_path, str)
        assert isinstance(thm_name, str)
        assert isinstance(thm_idx, int)
        self.search_result = search_result
        self.orig_file_path = orig_file_path
        self.thm_name = thm_name
        self.thm_idx = thm_idx

    def to_json(self) -> Any:
        return {
            "search_result": self.search_result.to_json(),
            "orig_file_path": self.orig_file_path,
            "thm_name": self.thm_name,
            "thm_idx": self.thm_idx,
        }

    def get_save_name(self, file_tree_loc: str = "") -> str:
        orig_file_basename = (
            self.orig_file_path.lstrip(file_tree_loc)
            .lstrip("/")
            .lstrip('"')
            .lstrip(DESIRED_PREFIX)
        )
        save_path_name = orig_file_basename.replace("/", "-").replace("\\", "-")
        save_name = f"{save_path_name}:{self.thm_name}:{self.thm_idx}.json"
        return save_name

    def save(self, out_dir: str, file_tree_loc: str = "") -> None:
        save_loc = os.path.join(out_dir, self.get_save_name(file_tree_loc))
        with open(save_loc, "w") as fout:
            fout.write(json.dumps(self.to_json(), indent=2))

    @classmethod
    def eval_from_json(cls, json_data: Any) -> EvalSearchResult:
        """Less precise version of from_json. Good for backward compat."""
        search_result_data = json_data["search_result"]
        search_result = SearchResult.eval_from_json(search_result_data)
        orig_file_path = json_data["orig_file_path"]
        thm_name = json_data["thm_name"]
        thm_idx = json_data["thm_idx"]
        return cls(search_result, orig_file_path, thm_name, thm_idx)

    @classmethod
    def from_json(cls, json_data: Any) -> EvalSearchResult:
        search_result_data = json_data["search_result"]
        search_result = SearchResult.from_json(search_result_data)
        orig_file_path = json_data["orig_file_path"]
        thm_name = json_data["thm_name"]
        thm_idx = json_data["thm_idx"]
        return cls(search_result, orig_file_path, thm_name, thm_idx)


@dataclass
class ThreadReturnObj:
    num_proofs_found: int
    num_proofs_attempted: int
    num_errors: int


# Need a proof
class Evaluator:
    def __init__(
        self,
        assignment_loc: str,
        results_loc: str,
        file_tree_loc: str,
        split: str,
        timeout: int,
        num_proofs: int,
        branching_factor: int,
        max_leaf_expansions: int,
        model_wrapper: ModelWrapper,
        node_score_type: type[NodeScore],
        coq_file_timeout: int = 60,
    ) -> None:
        assert type(assignment_loc) == str
        assert type(results_loc) == str
        assert type(split) == str
        assert type(timeout) == int
        assert type(num_proofs) == int
        assert type(max_leaf_expansions) == int
        assert type(branching_factor) == int
        assert isinstance(model_wrapper, ModelWrapper)
        assert type(node_score_type) == type
        self.assignments_loc = assignment_loc
        self.results_loc = results_loc
        self.file_tree_loc = file_tree_loc
        self.split = split
        self.timeout = timeout
        self.num_proofs = num_proofs
        self.branching_factor = branching_factor
        self.max_leaf_expansions = max_leaf_expansions
        self.model_wrapper = model_wrapper
        self.node_score_type = node_score_type
        self.coq_file_timeout = coq_file_timeout

    def proof_file_generator(self) -> Generator[tuple[str, str], None, None]:
        with open(self.assignments_loc, "r") as fin:
            assignment = json.load(fin)
        assert assignment_shape_expected(assignment)
        mapping_loc = os.path.join(self.file_tree_loc, FILE_MAPPING_NAME)
        with open(mapping_loc, "r") as fin:
            mapping = json.load(fin)
        assert mapping_shape_correct(mapping)
        assert self.split in SPLITS

        # eligible_files = assignment[self.split]
        # Found safe validation files manually. In the future will
        # be automated
        with open("safe_val.txt", "r") as fin:
            eligible_files = json.load(fin)

        for file in eligible_files:
            physical_path = mapping[file]
            yield file, physical_path

    def get_search_result(
        self,
        orig_file: str,
        proof_file: ProofFile,
        thm_idx: int,
        lm_example_conf: LmExampleConfig,
    ) -> SearchResult:
        with ProofManager(
            orig_file, proof_file, thm_idx, lm_example_conf
        ) as proof_manager:
            initial_check = proof_manager.check_proof("", [])
            if initial_check.tactic_result in (
                TacticResult.INVALID,
                TacticResult.COMPLETE,
            ):
                # TODO: thm name would be nice
                print(
                    f"Skipping {orig_file} with result {initial_check.tactic_result.name}."
                )
                raise ValueError(
                    f"Skipping {orig_file} with result {initial_check.tactic_result.name}."
                )
            searcher = SearchTreeManager(
                self.model_wrapper,
                proof_manager,
                self.node_score_type,
                self.branching_factor,
                self.max_leaf_expansions,
                self.timeout,
            )
            search_result = searcher.search()
        return search_result

    def search_thread(
        self,
        orig_file: str,
        hidden_file: str,
        thm_names_and_indices: list[tuple[str, int]],
        lm_example_conf: LmExampleConfig,
        result_hole: ThreadReturnObj,
    ) -> None:
        with ProofFile(hidden_file) as proof_file:
            for thm_name, thm_idx in thm_names_and_indices:
                try:
                    search_result = self.get_search_result(
                        orig_file, proof_file, thm_idx, lm_example_conf
                    )
                    eval_search_result = EvalSearchResult(
                        search_result, orig_file, thm_name, thm_idx
                    )
                    eval_search_result.search_result.search_tree.pretty_print(
                        verbose=False
                    )
                    eval_search_result.save(self.results_loc, self.file_tree_loc)
                    if search_result.found_proof():
                        result_hole.num_proofs_found += 1
                except:
                    error_str = traceback.format_exc()
                    error_loc = os.path.join(self.results_loc, "errors.txt")
                    with open(error_loc, "a") as fout:
                        fout.write(error_str + "\n\n")
                    result_hole.num_errors += 1
                finally:
                    result_hole.num_proofs_attempted += 1

    @staticmethod
    def __get_thm_name(step_text: str) -> Optional[str]:
        match lex(step_text):
            case [IdTok(name="Lemma"), IdTok(name=l), *_]:
                return l
            case [IdTok(name="Theorem"), IdTok(name=t), *_]:
                return t
            case _:
                return None

    def __get_thm_names_and_indices(self, file: str) -> list[tuple[str, int]]:
        thm_indices: list[tuple[str, int]] = []
        with CoqFile(file) as coq_file:
            cur_step = 0
            while cur_step < len(coq_file.steps):
                coq_file.exec(1)
                if coq_file.in_proof:
                    thm_name = self.__get_thm_name(coq_file.steps[cur_step].text)
                    if thm_name:
                        thm_indices.append((thm_name, cur_step))
                cur_step += 1
        return thm_indices

    def evaluate(self) -> None:
        file_generator = self.proof_file_generator()
        num_proof_attempts = 0
        num_correct_proofs = 0
        num_errors = 0
        lm_example_conf = self.model_wrapper.lm_example_config
        for _, physical_path in file_generator:
            thm_names_and_indices = self.__get_thm_names_and_indices(physical_path)
            if len(thm_names_and_indices) == 0:
                continue
            file_dirname = os.path.dirname(physical_path)
            file_basename = os.path.basename(physical_path)
            hidden_file = get_fresh_path(file_dirname, file_basename)

            thread_result = ThreadReturnObj(0, 0, 0)
            search_thread = Thread(
                target=self.search_thread,
                args=(
                    physical_path,
                    hidden_file,
                    thm_names_and_indices,
                    lm_example_conf,
                    thread_result,
                ),
            )

            search_thread.start()
            search_thread.join(
                timeout=(self.timeout * 1.5 * len(thm_names_and_indices) + 60)
            )
            num_correct_proofs += thread_result.num_proofs_found
            num_proof_attempts += thread_result.num_proofs_attempted
            num_errors += thread_result.num_errors

            print(f"Correct Proofs: {num_correct_proofs}")
            print(f"Proof Attempts: {num_proof_attempts}")
            print(f"Num Errors: {num_errors}")


def evaluate(evaluate_conf_loc: str) -> None:
    with open(evaluate_conf_loc, "r") as fin:
        evaluate_conf = load(fin, Loader=Loader)

    assignment_loc = evaluate_conf["assignment_loc"]
    results_loc = evaluate_conf["results_loc"]
    file_tree_loc = evaluate_conf["file_tree_loc"]
    split = evaluate_conf["split"]
    timeout = evaluate_conf["timeout"]
    num_proofs = evaluate_conf["num_proofs"]
    branching_factor = evaluate_conf["branching_factor"]
    max_leaf_expandsions = evaluate_conf["max_leaf_expansions"]

    model_wrapper_alias = evaluate_conf["model_wrapper"]
    model_wrapper_type = MODEL_WRAPPER_ALIASES[model_wrapper_alias]
    model_wrapper = model_wrapper_type.from_json(evaluate_conf[model_wrapper_alias])
    node_score_type = NODE_SCORE_ALIASES[evaluate_conf["node_score"]]

    if os.path.exists(results_loc):
        print(f"{results_loc} exists.", file=sys.stderr)
        exit(1)
    os.makedirs(results_loc)
    shutil.copy(evaluate_conf_loc, results_loc)

    # model_wrapper.get_recs(LmExample("hi", "there"), 2)

    evaluator = Evaluator(
        assignment_loc,
        results_loc,
        file_tree_loc,
        split,
        timeout,
        num_proofs,
        branching_factor,
        max_leaf_expandsions,
        model_wrapper,
        node_score_type,
    )

    evaluator.evaluate()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=("Run evaluation on a given model."))
    parser.add_argument("eval_config", help="Path to eval configuration file.")
    args = parser.parse_args(sys.argv[1:])
    evaluate(args.eval_config)
