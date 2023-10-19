from typing import Iterable, Callable

import sys, os
import json
from model_deployment.searcher import ProofSearchTree
from evaluation.evaluate import EvalSearchResult


def __get_json_file_names(dir: str) -> list[str]:
    all_files = os.listdir(dir)
    return [f for f in all_files if f.endswith(".json")]


def find_shared_proofs(eval_dirs: list[str]) -> set[str]:
    assert len(eval_dirs) > 0
    shared_proofs = set(__get_json_file_names(eval_dirs[0]))
    for eval_dir in eval_dirs[1:]:
        shared_proofs &= set(__get_json_file_names(eval_dir))
    return shared_proofs


def get_eval_results(eval_dir: str, proof_files: list[str]) -> list[EvalSearchResult]:
    eval_results: list[EvalSearchResult] = []
    for proof_file in proof_files:
        eval_data_loc = os.path.join(eval_dir, proof_file)
        with open(eval_data_loc, "r") as fin:
            eval_data = json.load(fin)
            eval_obj = EvalSearchResult.from_json(eval_data)
            eval_results.append(eval_obj)
    return eval_results


def __pos_expanded_key(e: EvalSearchResult) -> int:
    path_to_qed = e.search_result.search_tree.get_path_to_qed()
    assert len(path_to_qed) >= 2
    assert path_to_qed[-2].expanded is not None
    return path_to_qed[-2].expanded


def __pos_time_key(e: EvalSearchResult) -> float:
    assert e.search_result.qed_node is not None
    return e.search_result.qed_node.creation_time / 1e9


def get_sorted_successful_evals(
    eval_dir: str, proof_files: list[str], sort_key: Callable[[EvalSearchResult], float]
) -> list[EvalSearchResult]:
    eval_results = get_eval_results(eval_dir, proof_files)
    pos_eval_results = [e for e in eval_results if e.search_result.found_proof()]
    pos_eval_results.sort(key=sort_key)
    return pos_eval_results


def get_metric_and_num_proofs(
    eval_dir: str, proof_files: list[str], metric: Callable[[EvalSearchResult], float]
) -> tuple[list[float], list[int]]:
    metric_sorted_successful_evals = get_sorted_successful_evals(
        eval_dir, proof_files, metric
    )
    values: list[float] = []
    nums: list[int] = []
    for eval in metric_sorted_successful_evals:
        values.append(metric(eval))
        nums.append(len(values))
    return values, nums


def get_times_and_num_proofs(
    eval_dir: str, proof_files: list[str]
) -> tuple[list[float], list[int]]:
    return get_metric_and_num_proofs(eval_dir, proof_files, __pos_time_key)


def get_expansions_and_num_proofs(
    eval_dir: str, proof_files: list[str]
) -> tuple[list[float], list[int]]:
    return get_metric_and_num_proofs(eval_dir, proof_files, __pos_expanded_key)
