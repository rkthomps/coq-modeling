from __future__ import annotations
from typing import Iterable, Callable, Any, Optional
from dataclasses import dataclass

import math
import sys, os

from evaluation.evaluate import (
    EvalSearchResult,
    SuccessfulSearch,
)


SuccessMetric = Callable[[SuccessfulSearch], float]


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


@dataclass
class EvalDict:
    eval_name: str
    eval_path: str
    eval_objs: dict[str, EvalSearchResult]

    def sorted_successful_evals(
        self, metric: SuccessMetric
    ) -> list[tuple[EvalSearchResult, SuccessfulSearch, float]]:
        result: list[tuple[EvalSearchResult, SuccessfulSearch, float]] = []
        for _, obj in self.eval_objs.items():
            match obj.search_result:
                case SuccessfulSearch():
                    result.append((obj, obj.search_result, metric(obj.search_result)))
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
                if r.start <= len(obj.ground_truth_steps) <= r.end:
                    match obj.search_result:
                        case SuccessfulSearch():
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
        eval_objs: dict[str, EvalSearchResult] = {}
        for proof_name in shared_proofs:
            proof_path = os.path.join(path, EvalSearchResult.ATTEMPTS_NAME, proof_name)
            eval_obj = EvalSearchResult.load(proof_path, load_data_points=False)
            eval_objs[proof_name] = eval_obj
        return cls(name, path, eval_objs)


def get_combined_num_proofs_by_metric(
    eval_dicts: list[EvalDict], metric: SuccessMetric
) -> PlotInfo:
    combined_evals: list[tuple[EvalSearchResult, SuccessfulSearch]] = []
    for eval_dict in eval_dicts:
        for eval in eval_dict.eval_objs.values():
            match eval.search_result:
                case SuccessfulSearch():
                    combined_evals.append((eval, eval.search_result))
                case _:
                    pass

    counted_proofs: set[tuple[str, int]] = set()
    combined_evals.sort(key=lambda t: metric(t[1]))
    values: list[float] = []
    nums: list[int] = []
    for e, s in combined_evals:
        if (e.file.file, e.thm_idx) in counted_proofs:
            continue
        values.append(metric(s))
        nums.append(len(values))
        counted_proofs.add((e.file.file, e.thm_idx))
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


def expanded_key(s: SuccessfulSearch) -> int:
    path_to_qed = s.search_tree.root.get_path_to_qed()
    assert len(path_to_qed) >= 2
    assert path_to_qed[-2].expanded is not None
    return path_to_qed[-2].expanded


def time_key(s: SuccessfulSearch) -> float:
    return s.qed_node.creation_time / 1e9
