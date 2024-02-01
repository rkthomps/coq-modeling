from __future__ import annotations
from typing import Iterable, Callable, Any, Optional
from dataclasses import dataclass
from typeguard import typechecked
import multiprocessing

import argparse
import math
import sys, os
import json
import time

from evaluation.evaluate import (
    EvalSearchResult,
    SuccessfulSearch,
    FailedSearch,
    ErroredSearch,
)


@dataclass
class PlotInfo:
    xs: list[float]
    ys: list[int]
    name: str


@dataclass
class LengthRange:
    start: int
    end: int

    def label(self) -> str:
        return f"[{self.start}-{self.end}]"


class ProofRate:
    def __init__(self, successes: int, attempts: int) -> None:
        assert attempts > 0
        self.successes = successes
        self.attempts = attempts

    def __repr__(self) -> str:
        return f"Successes: {self.successes}, Attempts: {self.attempts}"

    def rate(self) -> float:
        return self.successes / self.attempts

    def margin(self) -> float:
        rate = self.rate()
        return 1.96 * math.sqrt(rate * (1 - rate) / self.attempts)


class SuccessResult:
    ALIAS = "success"

    def __init__(self, seconds: float, expansions: int) -> None:
        self.seconds = seconds
        self.expansions = expansions

    def to_json(self) -> Any:
        return {
            "seconds": self.seconds,
            "expansions": self.expansions,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> SuccessResult:
        seconds = json_data["seconds"]
        expansions = json_data["expansions"]
        return cls(seconds, expansions)


class FailedResult:
    ALIAS = "failure"

    def __init__(self, time_before_fail: float) -> None:
        self.time_before_fail = time_before_fail

    def to_json(self) -> Any:
        return {
            "time_before_fail": self.time_before_fail,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> FailedResult:
        return cls(json_data["time_before_fail"])


class ErrorResult:
    ALIAS = "error"

    def __init__(self, time_before_error: float) -> None:
        self.time_before_error = time_before_error

    def to_json(self) -> Any:
        return {"time_before_error": self.time_before_error}

    @classmethod
    def from_json(cls, json_data: Any) -> ErrorResult:
        return cls(json_data["time_before_error"])


SmallSearchResult = SuccessResult | FailedResult | ErrorResult

SuccessMetric = Callable[[SuccessResult], float]


class SmallResultNotFoundError(Exception):
    pass


def small_result_to_json(small_search_result: SmallSearchResult) -> Any:
    return {"alias": small_search_result.ALIAS} | small_search_result.to_json()


def small_result_from_json(json_data: Any) -> SmallSearchResult:
    attempted_alias = json_data["alias"]
    match attempted_alias:
        case SuccessResult.ALIAS:
            return SuccessResult.from_json(json_data)
        case FailedResult.ALIAS:
            return FailedResult.from_json(json_data)
        case ErrorResult.ALIAS:
            return ErrorResult.from_json(json_data)
        case _:
            raise SmallResultNotFoundError(f"{attempted_alias}")


def retrieve_small_result(eval_dir: str, proof_name: str) -> SmallEvalResult:
    large_path = os.path.join(eval_dir, EvalSearchResult.ATTEMPTS_NAME, proof_name)
    small_path = os.path.join(eval_dir, SmallEvalResult.SMALL_ATTEMPTS_NAME, proof_name)
    if os.path.exists(small_path):
        return SmallEvalResult.load(small_path)
    os.makedirs(
        os.path.join(eval_dir, SmallEvalResult.SMALL_ATTEMPTS_NAME), exist_ok=True
    )
    large_obj = EvalSearchResult.load(large_path)
    small_obj = SmallEvalResult.from_large_eval_result(large_obj)
    small_obj.save(small_path)
    return small_obj


@typechecked
class SmallEvalResult:
    SMALL_ATTEMPTS_NAME = "small-attempts"

    def __init__(
        self,
        small_search_result: SmallSearchResult,
        ground_truth_length: int,
        file: str,
        thm_idx: int,
    ) -> None:
        self.small_search_result = small_search_result
        self.ground_truth_length = ground_truth_length
        self.file = file
        self.thm_idx = thm_idx

    def to_json(self) -> Any:
        return {
            "small_search_result": small_result_to_json(self.small_search_result),
            "ground_truth_length": self.ground_truth_length,
            "file": self.file,
            "thm_idx": self.thm_idx,
        }

    def save(self, path: str) -> None:
        with open(path, "w") as fout:
            fout.write(json.dumps(self.to_json(), indent=2))

    @classmethod
    def from_large_eval_result(
        cls, large_eval_result: EvalSearchResult
    ) -> SmallEvalResult:
        match large_eval_result.search_result:
            case SuccessfulSearch():
                qed_node = large_eval_result.search_result.qed_node
                seconds = qed_node.creation_time / 1e9
                path_to_qed = (
                    large_eval_result.search_result.search_tree.root.get_path_to_qed()
                )
                assert len(path_to_qed) >= 2
                assert path_to_qed[-2].expanded is not None
                expanded = path_to_qed[-2].expanded
                small_search_result = SuccessResult(seconds, expanded)
            case FailedSearch():
                max_creation_time = (
                    large_eval_result.search_result.search_tree.root.get_last_node_time()
                )
                small_search_result = FailedResult(max_creation_time)
            case ErroredSearch():
                small_search_result = ErrorResult(
                    large_eval_result.search_result.error_after
                )
        return SmallEvalResult(
            small_search_result,
            len(large_eval_result.ground_truth_steps),
            large_eval_result.file.file,
            large_eval_result.thm_idx,
        )

    @classmethod
    def from_json(cls, json_data: Any) -> SmallEvalResult:
        small_search_result_data = json_data["small_search_result"]
        small_search_result = small_result_from_json(small_search_result_data)
        ground_truth_length = json_data["ground_truth_length"]
        file = json_data["file"]
        thm_idx = json_data["thm_idx"]
        return cls(small_search_result, ground_truth_length, file, thm_idx)

    @classmethod
    def load(cls, path: str) -> SmallEvalResult:
        with open(path, "r") as fin:
            json_data = json.load(fin)
            return SmallEvalResult.from_json(json_data)


@typechecked
@dataclass
class EvalDict:
    eval_name: str
    eval_path: str
    eval_objs: dict[str, SmallEvalResult]

    def was_successful(self, proof_name: str) -> bool:
        match self.eval_objs[proof_name].small_search_result:
            case SuccessResult():
                return True
            case FailedResult():
                return False
            case ErrorResult():
                return False

    def get_successful_times(self) -> list[float]:
        times: list[float] = []
        for _, obj in self.eval_objs.items():
            match obj.small_search_result:
                case SuccessResult():
                    times.append(obj.small_search_result.seconds)
                case _:
                    pass
        return times

    def get_failed_times(self) -> list[float]:
        times: list[float] = []
        for _, obj in self.eval_objs.items():
            match obj.small_search_result:
                case FailedResult():
                    times.append(obj.small_search_result.time_before_fail / 1e9)
                case _:
                    pass
        return times

    def filter(self, new_keys: set[str]) -> EvalDict:
        new_dict: dict[str, SmallEvalResult] = {}
        for k, v in self.eval_objs.items():
            if k in new_keys:
                new_dict[k] = v
        return EvalDict(self.eval_name, self.eval_path, new_dict)

    def sorted_successful_evals(
        self, metric: SuccessMetric
    ) -> list[tuple[SmallEvalResult, SuccessResult, float]]:
        result: list[tuple[SmallEvalResult, SuccessResult, float]] = []
        for _, obj in self.eval_objs.items():
            match obj.small_search_result:
                case SuccessResult():
                    result.append(
                        (obj, obj.small_search_result, metric(obj.small_search_result))
                    )
                case _:
                    pass
        return sorted(result, key=lambda x: x[2])

    def get_num_proofs_by_metric(self, metric: SuccessMetric) -> PlotInfo:
        sorted_evals = self.sorted_successful_evals(metric)
        values: list[float] = []
        nums: list[int] = []
        for _, _, value in sorted_evals:
            values.append(value)
            nums.append(len(values))
        return PlotInfo(values, nums, self.eval_name)

    def get_proof_rate_by_length(self, ranges: list[LengthRange]) -> list[ProofRate]:
        rates: list[ProofRate] = []
        for r in ranges:
            successes = 0
            attempts = 0
            for _, obj in self.eval_objs.items():
                if r.start <= obj.ground_truth_length <= r.end:
                    match obj.small_search_result:
                        case SuccessResult():
                            successes += 1
                        case _:
                            pass
                    attempts += 1
            rates.append(ProofRate(successes, attempts))
        return rates

    @classmethod
    def from_shared_proofs(
        cls, name: str, path: str, shared_proofs: set[str]
    ) -> EvalDict:
        eval_objs: dict[str, SmallEvalResult] = {}
        for proof_name in shared_proofs:
            small_obj = retrieve_small_result(path, proof_name)
            eval_objs[proof_name] = small_obj
        return cls(name, path, eval_objs)


def num_proofs(eval_dicts: list[EvalDict]) -> int:
    assert len(eval_dicts) > 0
    tentative_num = len(eval_dicts[0].eval_objs)
    for eval_dict in eval_dicts:
        assert tentative_num == len(eval_dict.eval_objs)
    return tentative_num


def filter_all_successful(
    shared_proofs: set[str], eval_dicts: list[EvalDict]
) -> set[str]:
    success_keys: set[str] = set()
    for proof in shared_proofs:
        all_successful = True
        for eval_dict in eval_dicts:
            if not eval_dict.was_successful(proof):
                all_successful = False
                break
        if all_successful:
            success_keys.add(proof)
    return success_keys


def filter_all_failure(shared_proofs: set[str], eval_dicts: list[EvalDict]) -> set[str]:
    failure_keys: set[str] = set()
    for proof in shared_proofs:
        all_failed = True
        for eval_dict in eval_dicts:
            if not isinstance(
                eval_dict.eval_objs[proof].small_search_result, FailedResult
            ):
                all_failed = False
                break
        if all_failed:
            failure_keys.add(proof)
    return failure_keys


def filter_all_no_error(
    shared_proofs: set[str], eval_dicts: list[EvalDict]
) -> set[str]:
    no_error_keys: set[str] = set()
    for proof in shared_proofs:
        all_no_error = True
        for eval_dict in eval_dicts:
            match eval_dict.eval_objs[proof].small_search_result:
                case ErrorResult():
                    all_no_error = False
                    break
                case _:
                    continue
        if all_no_error:
            no_error_keys.add(proof)
    return no_error_keys


def get_combined_num_proofs_by_metric(
    eval_dicts: list[EvalDict], metric: SuccessMetric
) -> PlotInfo:
    combined_evals: list[tuple[SmallEvalResult, SuccessResult]] = []
    for eval_dict in eval_dicts:
        for eval in eval_dict.eval_objs.values():
            match eval.small_search_result:
                case SuccessResult():
                    combined_evals.append((eval, eval.small_search_result))
                case _:
                    pass

    counted_proofs: set[tuple[str, int]] = set()
    combined_evals.sort(key=lambda t: metric(t[1]))
    values: list[float] = []
    nums: list[int] = []
    for e, s in combined_evals:
        if (e.file, e.thm_idx) in counted_proofs:
            continue
        values.append(metric(s))
        nums.append(len(values))
        counted_proofs.add((e.file, e.thm_idx))
    return PlotInfo(values, nums, "Combined")


def __get_json_file_names(dir: str) -> list[str]:
    all_files = os.listdir(os.path.join(dir, EvalSearchResult.ATTEMPTS_NAME))
    return [f for f in all_files if f.endswith(".json")]


def find_shared_proofs(eval_dirs: list[str]) -> set[str]:
    assert len(eval_dirs) > 0
    shared_proofs = set(__get_json_file_names(eval_dirs[0]))
    for eval_dir in eval_dirs[1:]:
        shared_proofs &= set(__get_json_file_names(eval_dir))
    return shared_proofs


def expanded_key(s: SuccessResult) -> int:
    return s.expansions


def time_key(s: SuccessResult) -> float:
    return s.seconds


def get_small_eval_retrieve_args(eval_dir: str) -> list[tuple[str, str]]:
    attempts_loc = os.path.join(eval_dir, EvalSearchResult.ATTEMPTS_NAME)
    attempt_list: list[tuple[str, str]] = []
    for attempt in os.listdir(attempts_loc):
        attempt_list.append((eval_dir, attempt))
    return attempt_list


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        "Get small results for analysis from top level eval directory."
    )
    parser.add_argument("eval_dir", help="Directory resulting from run_eval.py.")
    parser.add_argument(
        "n_procs", type=int, help="Number of processes to use to create small results."
    )
    args = parser.parse_args(sys.argv[1:])
    retrieve_args = get_small_eval_retrieve_args(args.eval_dir)
    with multiprocessing.Pool(args.n_procs) as pool:
        pool.starmap(retrieve_small_result, retrieve_args)
