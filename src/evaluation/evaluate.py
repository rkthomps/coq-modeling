from __future__ import annotations
from typing import Any, Optional
from dataclasses import dataclass
import json
import time
import sys, os
import argparse
import shutil
import traceback
from threading import Thread

from typeguard import typechecked
from yaml import load, Loader


from coqpyt.coq.base_file import CoqFile
from coqpyt.coq.proof_file import ProofFile

from tactic_gen.step_parser import lex, IdTok
from data_management.splits import DataSplit, str2split, Split, FileInfo
from data_management.create_lm_dataset import LmExampleConfig
from model_deployment.searcher import (
    SearchTreeManager,
    SuccessfulSearch,
    FailedSearch,
    ErroredSearch,
    SearchResult,
    search_result_from_json,
)
from model_deployment.proof_manager import (
    ProofManager,
    get_fresh_path,
    TacticResult,
)
from model_deployment.model_wrapper import ModelWrapper, MODEL_WRAPPER_ALIASES
from model_deployment.node_score import NodeScore, NODE_SCORE_ALIASES


@typechecked
class EvalSearchResult:
    def __init__(
        self,
        search_result: SearchResult,
        file: FileInfo,
        thm_name: str,
        thm_idx: int,
        ground_truth_steps: list[str],
    ) -> None:
        self.search_result = search_result
        self.file = file
        self.thm_name = thm_name
        self.thm_idx = thm_idx
        self.ground_truth_steps = ground_truth_steps

    def to_json(self) -> Any:
        return {
            "search_result": self.search_result.to_json(),
            "file": self.file,
            "thm_name": self.thm_name,
            "thm_idx": self.thm_idx,
            "ground_truth_steps": self.ground_truth_steps,
        }

    def get_save_name(self) -> str:
        save_name = f"{self.file.dp_name}:{self.thm_name}:{self.thm_idx}.json"
        return save_name

    def get_ground_truth_str(self) -> str:
        return "".join(self.ground_truth_steps)

    def save(self, out_dir: str) -> None:
        save_loc = os.path.join(out_dir, self.get_save_name())
        with open(save_loc, "w") as fout:
            fout.write(json.dumps(self.to_json(), indent=2))

    @classmethod
    def from_json(cls, json_data: Any) -> EvalSearchResult:
        search_result_data = json_data["search_result"]
        search_result = search_result_from_json(search_result_data)
        orig_file_path = json_data["orig_file_path"]
        thm_name = json_data["thm_name"]
        thm_idx = json_data["thm_idx"]
        ground_truth_steps = json_data["ground_truth_steps"]
        return cls(search_result, orig_file_path, thm_name, thm_idx, ground_truth_steps)

    @classmethod
    def load(cls, path: str) -> EvalSearchResult:
        with open(path, "r") as fin:
            json_data = json.load(fin)
            return cls.from_json(json_data)


@dataclass
class ThreadReturnObj:
    num_proofs_found: int
    num_proofs_attempted: int
    num_errors: int


# Need a proof
@typechecked
class Evaluator:
    def __init__(
        self,
        data_split: DataSplit,
        results_loc: str,
        data_loc: str,
        split: Split,
        timeout: int,
        num_proofs: int,
        branching_factor: int,
        max_leaf_expansions: int,
        model_wrapper: ModelWrapper,
        node_score_type: type[NodeScore],
        coq_file_timeout: int = 60,
    ) -> None:
        self.data_split = data_split
        self.results_loc = results_loc
        self.data_loc = data_loc
        self.split = split
        self.timeout = timeout
        self.num_proofs = num_proofs
        self.branching_factor = branching_factor
        self.max_leaf_expansions = max_leaf_expansions
        self.model_wrapper = model_wrapper
        self.node_score_type = node_score_type
        self.coq_file_timeout = coq_file_timeout

    def get_search_result(
        self,
        orig_file: str,
        proof_file: ProofFile,
        thm_idx: int,
        lm_example_conf: LmExampleConfig,
    ) -> SuccessfulSearch | FailedSearch:
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

    @staticmethod
    def __get_ground_truth(proof_file: ProofFile, thm_idx: int) -> list[str]:
        step_after = proof_file.steps[thm_idx + 1]
        for proof in proof_file.proofs:
            if proof.steps[0].ast.range == step_after.ast.range:
                return [s.text for s in proof.steps]
        raise ValueError(f"No proof corresponding to thm {thm_idx}.")

    def search_thread(
        self,
        file: FileInfo,
        hidden_file: str,
        orig_file: str,
        thm_names_and_indices: list[tuple[str, int]],
        lm_example_conf: LmExampleConfig,
        result_hole: ThreadReturnObj,
    ) -> None:
        with ProofFile(hidden_file) as proof_file:
            for thm_name, thm_idx in thm_names_and_indices:
                start = time.time()
                try:
                    search_result = self.get_search_result(
                        orig_file, proof_file, thm_idx, lm_example_conf
                    )
                    search_result.search_tree.pretty_print(verbose=False)
                except:
                    error_str = traceback.format_exc()
                    stop = time.time()
                    search_result = ErroredSearch(error_str, stop - start)
                finally:
                    ground_truth = self.__get_ground_truth(proof_file, thm_idx)
                    eval_search_result = EvalSearchResult(
                        search_result,
                        file,
                        thm_name,
                        thm_idx,
                        ground_truth,
                    )
                    eval_search_result.save(self.results_loc)

                    match search_result:
                        case SuccessfulSearch():
                            result_hole.num_proofs_found += 1
                        case ErroredSearch():
                            result_hole.num_errors += 1
                        case _:
                            pass
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

    def __was_success(self, search_loc: str) -> bool:
        with open(search_loc, "r") as fin:
            result_data = json.load(fin)
            e_obj = EvalSearchResult.eval_from_json(result_data)
            return e_obj.search_result.found_proof()

    def evaluate(self) -> None:
        eval_files = self.data_split.get_file_list(self.data_loc, self.split)
        num_proof_attempts = 0
        num_correct_proofs = 0
        num_errors = 0
        lm_example_conf = self.model_wrapper.lm_example_config
        for file in eval_files:
            physical_path = os.path.join(self.data_loc, file.file)
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
                    file,
                    hidden_file,
                    physical_path,
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


def __check_continue() -> bool:
    while True:
        s = input("Continue Anyway? :")
        if s.startswith("y"):
            return True
        if s.startswith("n"):
            return False
        print("Respond with yes or no.")


def evaluate(evaluate_conf_loc: str) -> None:
    with open(evaluate_conf_loc, "r") as fin:
        evaluate_conf = load(fin, Loader=Loader)

    data_split = DataSplit.load(evaluate_conf["data_split_loc"])
    results_loc: str = evaluate_conf["results_loc"]
    data_loc: str = evaluate_conf["data_loc"]
    split = str2split(evaluate_conf["split"])
    timeout: int = evaluate_conf["timeout"]
    num_proofs: int = evaluate_conf["num_proofs"]
    branching_factor: int = evaluate_conf["branching_factor"]
    max_leaf_expandsions: int = evaluate_conf["max_leaf_expansions"]

    model_wrapper_alias: str = evaluate_conf["model_wrapper"]
    model_wrapper_type: type[ModelWrapper] = MODEL_WRAPPER_ALIASES[model_wrapper_alias]
    model_wrapper: ModelWrapper = model_wrapper_type.from_json(
        evaluate_conf[model_wrapper_alias]
    )
    node_score_type: type[NodeScore] = NODE_SCORE_ALIASES[evaluate_conf["node_score"]]

    if os.path.exists(results_loc):
        print(f"WARNING: {results_loc} exists. Continue anyway?", file=sys.stderr)
        if not __check_continue():
            raise ValueError("Result directory already exists!")
    else:
        os.makedirs(results_loc)
        shutil.copy(evaluate_conf_loc, results_loc)

    # model_wrapper.get_recs(LmExample("hi", "there"), 2)

    evaluator = Evaluator(
        data_split,
        results_loc,
        data_loc,
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
