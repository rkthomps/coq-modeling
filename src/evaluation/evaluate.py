from __future__ import annotations
from typing import Any, Optional, Generator
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

from data_management.splits import FileInfo
from model_deployment.searcher import (
    SearchTreeManager,
    SuccessfulSearch,
    FailedSearch,
    ErroredSearch,
    SearchResult,
    search_result_from_json,
    search_result_to_json,
)
from model_deployment.proof_manager import (
    ProofManager,
)
from model_deployment.model_wrapper import ModelWrapper, wrapper_from_conf
from model_deployment.node_score import NodeScore, NODE_SCORE_ALIASES

from evaluation.eval_set import DataSplitEvalSet, ProofInfo
from util.util import get_basic_logger

_logger = get_basic_logger(__name__)


@typechecked
class EvalSearchResult:
    ATTEMPTS_NAME = "attempts"

    def __init__(
        self,
        search_result: SearchResult,
        file: FileInfo,
        thm_idx: int,
        statement: str,
        ground_truth_steps: list[str],
    ) -> None:
        self.search_result = search_result
        self.file = file
        self.thm_idx = thm_idx
        self.statement = statement
        self.ground_truth_steps = ground_truth_steps

    def to_json(self) -> Any:
        return {
            "search_result": search_result_to_json(self.search_result),
            "file": self.file.to_json(),
            "thm_idx": self.thm_idx,
            "statement": self.statement,
            "ground_truth_steps": self.ground_truth_steps,
        }

    @classmethod
    def save_path(cls, dp_name: str, thm_idx: int, out_dir: str) -> str:
        save_name = f"{dp_name}:{thm_idx}.json"
        return os.path.join(out_dir, cls.ATTEMPTS_NAME, save_name)

    def get_ground_truth_str(self) -> str:
        return "".join(self.ground_truth_steps)

    def save(self, out_dir: str) -> None:
        os.makedirs(os.path.join(out_dir, self.ATTEMPTS_NAME), exist_ok=True)
        save_loc = self.save_path(self.file.dp_name, self.thm_idx, out_dir)
        with open(save_loc, "w") as fout:
            fout.write(json.dumps(self.to_json(), indent=2))

    @classmethod
    def from_json(cls, json_data: Any) -> EvalSearchResult:
        search_result_data = json_data["search_result"]
        search_result = search_result_from_json(search_result_data)
        file = FileInfo.from_json(json_data["file"])
        thm_idx = json_data["thm_idx"]
        statement = json_data["statement"]
        ground_truth_steps = json_data["ground_truth_steps"]
        return cls(search_result, file, thm_idx, statement, ground_truth_steps)

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
        results_loc: str,
        eval_set: DataSplitEvalSet,
        timeout: int,
        branching_factor: int,
        max_leaf_expansions: int,
        model_wrapper: ModelWrapper,
        node_score_type: type[NodeScore],
        coq_file_timeout: int = 60,
    ) -> None:
        self.results_loc = results_loc
        self.eval_set = eval_set
        self.timeout = timeout
        self.branching_factor = branching_factor
        self.max_leaf_expansions = max_leaf_expansions
        self.model_wrapper = model_wrapper
        self.node_score_type = node_score_type
        self.coq_file_timeout = coq_file_timeout

    @classmethod
    def from_conf(cls, conf: Any) -> Evaluator:
        results_loc = conf["results_loc"]
        eval_set = DataSplitEvalSet.from_conf(conf["eval_set"])
        timeout = conf["timeout"]
        branching_factor = conf["branching_factor"]
        max_leaf_expansions = conf["max_leaf_expansions"]
        model_wrapper = wrapper_from_conf(conf["model_wrapper"])
        node_score_type = NODE_SCORE_ALIASES[conf["node_score_type"]]
        return cls(
            results_loc,
            eval_set,
            timeout,
            branching_factor,
            max_leaf_expansions,
            model_wrapper,
            node_score_type,
        )

    def get_search_result(self, proof: ProofInfo) -> SuccessfulSearch | FailedSearch:
        with ProofManager(
            proof.file_loc, proof.proof_file, proof.idx, self.model_wrapper.formatter
        ) as proof_manager:
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
        file: FileInfo,
        result_hole: ThreadReturnObj,
    ) -> None:
        "This is ugly but I want the evaluation to not crash."
        try:
            proof_gen = self.eval_set.get_proof_gen(file)
        except:
            error_str = traceback.format_exc()
            _logger.error(f"Could not evaluate {file.file} with error: {error_str}")
            return
        while True:
            try:
                proof = next(proof_gen)
            except StopIteration:
                break
            except:
                error_str = traceback.format_exc()
                _logger.error(
                    f"Trouble getting next proof in file {file.file} with error {error_str}"
                )
                continue
            save_path = EvalSearchResult.save_path(
                file.dp_name, proof.idx, self.results_loc
            )
            if os.path.exists(save_path):
                _logger.info(f"{save_path} exists. Continuing.")
                continue
            statement = proof.statement()
            ground_truth = proof.ground_truth_steps()
            start = time.time()
            try:
                search_result = self.get_search_result(proof)
            except:
                error_str = traceback.format_exc()
                stop = time.time()
                search_result = ErroredSearch(error_str, stop - start)
            finally:
                eval_search_result = EvalSearchResult(
                    search_result,
                    file,
                    proof.idx,
                    statement,
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

    def evaluate(self) -> None:
        num_proof_attempts = 0
        num_correct_proofs = 0
        num_errors = 0
        for file in self.eval_set.get_file_gen():
            try:
                file_timeout = self.timeout * 1.5 * self.eval_set.rough_proof_count(file)
            except FileNotFoundError:
                _logger.warning(f"{file.file} not found.")
                continue
            _logger.debug(f"Giving {file.file} {file_timeout} seconds.")
            thread_result = ThreadReturnObj(0, 0, 0)
            search_thread = Thread(
                target=self.search_thread, args=(file, thread_result)
            )
            search_thread.start()
            search_thread.join(timeout=file_timeout)
            num_correct_proofs += thread_result.num_proofs_found
            num_proof_attempts += thread_result.num_proofs_attempted
            num_errors += thread_result.num_errors

            _logger.info(f"Correct Proofs: {num_correct_proofs}")
            _logger.info(f"Proof Attempts: {num_proof_attempts}")
            _logger.info(f"Num Errors: {num_errors}")


def evaluate(evaluate_conf_loc: str) -> None:
    with open(evaluate_conf_loc, "r") as fin:
        evaluate_conf = load(fin, Loader=Loader)
    evaluator = Evaluator.from_conf(evaluate_conf)
    evaluator.evaluate()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=("Run evaluation on a given model."))
    parser.add_argument("eval_config", help="Path to eval configuration file.")
    args = parser.parse_args(sys.argv[1:])
    evaluate(args.eval_config)
