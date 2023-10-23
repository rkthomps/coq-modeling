from __future__ import annotations
from typing import Iterable, Callable, Any

from functools import reduce

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


def get_eval_results(eval_dir: str, proof_files: set[str]) -> list[EvalSearchResult]:
    eval_results: list[EvalSearchResult] = []
    for proof_file in proof_files:
        eval_data_loc = os.path.join(eval_dir, proof_file)
        with open(eval_data_loc, "r") as fin:
            eval_data = json.load(fin)
            eval_obj = EvalSearchResult.eval_from_json(eval_data)
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


def get_successful_evals(eval_dir: str, proof_files: set[str]) -> set[str]:
    eval_results = get_eval_results(eval_dir, proof_files)
    sucessful_proofs: set[str] = set()
    for pf in proof_files:
        with open(os.path.join(eval_dir, pf), "r") as fin:
            eval_data = json.load(fin)
            eval_obj = EvalSearchResult.eval_from_json(eval_data)
            if eval_obj.search_result.found_proof():
                sucessful_proofs.add(pf)
    return sucessful_proofs


def get_sorted_successful_evals(
    eval_dir: str, proof_files: set[str], sort_key: Callable[[EvalSearchResult], float]
) -> list[EvalSearchResult]:
    eval_results = get_eval_results(eval_dir, proof_files)
    pos_eval_results = [e for e in eval_results if e.search_result.found_proof()]
    pos_eval_results.sort(key=sort_key)
    return pos_eval_results


def get_metric_and_num_proofs(
    eval_dir: str, proof_files: set[str], metric: Callable[[EvalSearchResult], float]
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
    eval_dir: str, proof_files: set[str]
) -> tuple[list[float], list[int]]:
    return get_metric_and_num_proofs(eval_dir, proof_files, __pos_time_key)


def get_expansions_and_num_proofs(
    eval_dir: str, proof_files: set[str]
) -> tuple[list[float], list[int]]:
    return get_metric_and_num_proofs(eval_dir, proof_files, __pos_expanded_key)


class ModelStats:
    def __init__(
        self,
        name: str,
        proofs_found: int,
        dominated_by: list[str],
        unique_proofs_found: set[str],
    ) -> None:
        self.name = name
        self.proofs_found = proofs_found
        self.dominated_by = dominated_by
        self.unique_proofs_found = unique_proofs_found

    def __repr__(self) -> str:
        return (
            f"------------ {self.name} -----------------\n"
            f"Number of proofs found: {self.proofs_found}\n"
            f"Dominated by: {self.dominated_by}\n"
            f"Number of unique proofs found: {len(self.unique_proofs_found)}\n"
        )

    @classmethod
    def create(
        cls,
        eval_dirs: list[tuple[str, str]],
        successful_proofs_by_eval: list[set[str]],
        model_index: int,
    ) -> ModelStats:
        assert len(eval_dirs) == len(successful_proofs_by_eval)
        assert 0 <= model_index < len(eval_dirs)
        dominated_by: list[str] = []
        union_others: set[str] = set()
        for i in range(len(eval_dirs)):
            if i == model_index:
                continue
            if successful_proofs_by_eval[i].issuperset(
                successful_proofs_by_eval[model_index]
            ):
                dominated_by.append(eval_dirs[i][NAME_IDX])
            union_others |= successful_proofs_by_eval[i]
        proofs_found = len(successful_proofs_by_eval[model_index])
        unique_proofs_found = successful_proofs_by_eval[model_index].difference(
            union_others
        )
        name = eval_dirs[model_index][NAME_IDX]
        return cls(name, proofs_found, dominated_by, unique_proofs_found)


def get_fine_grained_comparison_stats(
    eval_dirs: list[tuple[str, str]], proof_files: set[str]
) -> None:
    print(f"Total Number of Theorems: {len(proof_files)}.")

    successful_proofs_by_eval: list[set[str]] = []

    for eval_name, eval_dir in eval_dirs:
        successful_evals = get_successful_evals(eval_dir, proof_files)
        successful_proofs_by_eval.append(successful_evals)

    union_proofs = reduce(set.union, successful_proofs_by_eval)
    print(f"Cardinality of union of all proofs found: {len(union_proofs)}")

    model_stats_list = [
        ModelStats.create(eval_dirs, successful_proofs_by_eval, i)
        for i in range(len(eval_dirs))
    ]
    summary_strings = [repr(s) for s in model_stats_list]

    print("".join(summary_strings))


NAME_IDX = 0
PATH_IDX = 1


def assemble_coq_file_contents(
    eval_dirs: list[tuple[str, str]], proof_name: str
) -> str:
    assert len(eval_dirs) > 0
    eval_paths = [d[PATH_IDX] for d in eval_dirs]
    all_eval_results = [get_eval_results(p, {proof_name})[0] for p in eval_paths]
    proof_prefix = all_eval_results[0].proof_prefix

    suffix_strs: list[str] = []
    for i, result in enumerate(all_eval_results):
        if result.search_result.found_proof():
            result_str = "Correct"
            attempt_str = result.search_result.get_proof()
        else:
            result_str = "Incorrect"
            deep_node, _ = result.search_result.search_tree.get_deepest_node()
            attempt_str = deep_node.combined_model_tactics

        suffix_strs.append(
            f"\n\n(* ----- {eval_dirs[i][NAME_IDX]} {result_str} proof -----\n {attempt_str} *)"
        )
    return proof_prefix + "".join(suffix_strs)


def unique_thms_to_files(eval_dirs: list[tuple[str, str]], output_loc: str) -> None:
    if os.path.exists(output_loc):
        print(f"{output_loc} exists.", file=sys.stderr)
        exit(1)
    eval_paths = [eval_dir_tup[PATH_IDX] for eval_dir_tup in eval_dirs]
    shared_thms = find_shared_proofs(eval_paths)
    successful_evals = [get_successful_evals(p, shared_thms) for p in eval_paths]
    model_stats_list = [
        ModelStats.create(eval_dirs, successful_evals, i) for i in range(len(eval_dirs))
    ]

    for i, model_stats in enumerate(model_stats_list):
        if len(model_stats.unique_proofs_found) == 0:
            continue
        dir_name = os.path.join(output_loc, eval_dirs[i][NAME_IDX])
        os.makedirs(dir_name)
        for unique_proof in model_stats.unique_proofs_found:
            v_name = EvalSearchResult.name_to_v_file(unique_proof)
            proof_out_loc = os.path.join(dir_name, v_name)
            proof_contents = assemble_coq_file_contents(eval_dirs, unique_proof)
            with open(proof_out_loc, "w") as fout:
                fout.write(proof_contents)


if __name__ == "__main__":
    EVAL_DIRS = [
        ("Base", "/home/ubuntu/coq-modeling/evals/eval/codellama-7b-base"),
        (
            "Base with Premises",
            "/home/ubuntu/coq-modeling/evals/eval/codellama-7b-base-premise",
        ),
        ("Fine-Tuned", "/home/ubuntu/coq-modeling/evals/eval/codellama-7b-basic"),
        (
            "Fine-Tuned with Premises",
            "/home/ubuntu/coq-modeling/evals/eval/codellama-7b-premise",
        ),
    ]
    out_loc = "/home/ubuntu/coq-modeling/evals/examples"
    unique_thms_to_files(EVAL_DIRS, out_loc)
