from __future__ import annotations
from typing import Generator

import functools
from pathlib import Path
from dataclasses import dataclass

from model_deployment.prove import (
    Summary,
    load_results,
    ClassicalSummary,
    StraightLineSummary,
)


@dataclass
class EvalDesc:
    alias: str
    path_name: str


@dataclass
class SuccessfulSummary:
    file: Path
    theorem: str
    theorem_id: str
    search_time: float
    model_time: float
    attempts: int


@dataclass
class EvalData:
    alias: str
    results: list[Summary]

    def get_proof_set(self, include_errors: bool = True) -> set[ProofPair]:
        return set(
            [
                ProofPair(str(r.file), r.theorem_id)
                for r in self.results
                if r.model_time is not None or include_errors
            ]
        )

    def get_successful_searches(self) -> list[SuccessfulSummary]:
        successes: list[SuccessfulSummary] = []
        for r in self.results:
            if r.success:
                assert r.search_time is not None
                assert r.model_time is not None
                match r:
                    case ClassicalSummary():
                        assert r.search_steps is not None
                        num_attempts = r.search_steps
                    case StraightLineSummary():
                        assert r.attempts is not None
                        num_attempts = len(r.attempts)

                successes.append(
                    SuccessfulSummary(
                        r.file,
                        r.theorem,
                        r.theorem_id,
                        r.search_time,
                        r.model_time,
                        num_attempts,
                    )
                )
        return successes

    def get_model_time_points(self) -> list[PlotPoint]:
        successes = self.get_successful_searches()
        successes.sort(key=lambda x: x.model_time)
        return [PlotPoint(s.model_time, i + 1) for i, s in enumerate(successes)]

    def get_time_points(self) -> list[PlotPoint]:
        successes = self.get_successful_searches()
        successes.sort(key=lambda x: x.search_time)
        return [PlotPoint(s.search_time, i + 1) for i, s in enumerate(successes)]

    def get_attempts_points(self) -> list[PlotPoint]:
        successes = self.get_successful_searches()
        successes.sort(key=lambda x: x.attempts)
        return [PlotPoint(s.attempts, i + 1) for i, s in enumerate(successes)]

    def filter_to_proofs(self, proofs: set[ProofPair]) -> EvalData:
        new_results = [
            r for r in self.results if ProofPair(str(r.file), r.theorem_id) in proofs
        ]
        return EvalData(self.alias, new_results)

    def get_error_fraction(self) -> float:
        num_errors = 0
        for r in self.results:
            if r.search_time is None:
                num_errors += 1
        return num_errors / len(self.results)


@dataclass
class ProofPair:
    file_name: str
    theorem_id: str

    def __hash__(self) -> int:
        return hash((self.file_name, self.theorem_id))


@dataclass
class PlotPoint:
    x: float
    y: float


@dataclass
class TwoEvalSubsets:
    one_only: set[ProofPair]
    two_only: set[ProofPair]
    one_two: set[ProofPair]


@dataclass
class ThreeEvalSubsets:
    one_only: set[ProofPair]
    two_only: set[ProofPair]
    three_only: set[ProofPair]
    one_two: set[ProofPair]
    one_three: set[ProofPair]
    two_three: set[ProofPair]
    one_two_three: set[ProofPair]


def get_two_eval_subsets(
    evals: list[EvalData], eval1_alias: str, eval2_alias: str
) -> TwoEvalSubsets:
    eval1_list = [e for e in evals if e.alias == eval1_alias]
    assert len(eval1_list) == 1
    eval2_list = [e for e in evals if e.alias == eval2_alias]
    assert len(eval2_list) == 1

    e1 = eval1_list[0]
    e2 = eval2_list[0]
    e1_successes = set(
        [ProofPair(str(s.file), s.theorem_id) for s in e1.get_successful_searches()]
    )
    e2_successes = set(
        [ProofPair(str(s.file), s.theorem_id) for s in e2.get_successful_searches()]
    )
    return TwoEvalSubsets(
        e1_successes - e2_successes,
        e2_successes - e1_successes,
        e1_successes & e2_successes,
    )


def get_eval(evals: list[EvalData], alias: str) -> EvalData:
    eval_list = [e for e in evals if e.alias == alias]
    assert len(eval_list) == 1
    return eval_list[0]


def get_three_eval_subets(
    evals: list[EvalData], eval1_alias: str, eval2_alias: str, eval3_alias
) -> ThreeEvalSubsets:
    e1 = get_eval(evals, eval1_alias)
    e2 = get_eval(evals, eval2_alias)
    e3 = get_eval(evals, eval3_alias)

    e1_successes = set(
        [ProofPair(str(s.file), s.theorem_id) for s in e1.get_successful_searches()]
    )
    e2_successes = set(
        [ProofPair(str(s.file), s.theorem_id) for s in e2.get_successful_searches()]
    )
    e3_successes = set(
        [ProofPair(str(s.file), s.theorem_id) for s in e3.get_successful_searches()]
    )

    return ThreeEvalSubsets(
        e1_successes - e2_successes - e3_successes,
        e2_successes - e1_successes - e3_successes,
        e3_successes - e1_successes - e2_successes,
        e1_successes & e2_successes - e3_successes,
        e1_successes & e3_successes - e2_successes,
        e2_successes & e3_successes - e1_successes,
        e1_successes & e2_successes & e3_successes,
    )


def count_total_successes(evals: list[EvalData]) -> int:
    success_set: set[tuple[Path, str]] = set()
    for e in evals:
        success_set |= set(
            [(s.file, s.theorem_id) for s in e.get_successful_searches()]
        )
    return len(success_set)


def load_evals(eval_descs: list[EvalDesc], results_loc: Path) -> list[EvalData]:
    evals: list[EvalData] = []
    for eval_desc in eval_descs:
        eval_data = EvalData(
            eval_desc.alias, load_results(results_loc / eval_desc.path_name)
        )
        evals.append(eval_data)
    return evals


def find_mutual_proofs(
    evals: list[EvalData], include_errors: bool = True
) -> set[ProofPair]:
    if 0 == len(evals):
        return set()
    inter_proof_set = evals[0].get_proof_set(include_errors)
    for e in evals[1:]:
        inter_proof_set &= e.get_proof_set(include_errors)
    return inter_proof_set


def results_to_proof_map(results: list[Summary]) -> dict[ProofPair, Summary]:
    result_map: dict[ProofPair, Summary] = {}
    for r in results:
        key = ProofPair(str(r.file), r.theorem)
        if key in result_map:
            raise ValueError("Expected a unique set of proofs.")
        result_map[key] = r
    return result_map


def a_beats_b_generator(
    es: list[EvalData], e1_alias: str, e2_alias: str
) -> Generator[tuple[ProofPair, Summary, Summary], None, None]:
    e1 = get_eval(es, e1_alias)
    e2 = get_eval(es, e2_alias)
    e2_map = results_to_proof_map(e2.results)
    for r in e1.results:
        if not r.success:
            continue
        key = ProofPair(str(r.file), r.theorem)
        e2_result = e2_map[key]
        if not e2_result.success:
            yield key, r, e2_result
