from __future__ import annotations

import functools
from pathlib import Path
from dataclasses import dataclass

from model_deployment.prove import Summary
from model_deployment.run_proofs import load_results
from model_deployment.prove import ClassicalSummary, MCTSSummary, StraightLineSummary


@dataclass
class EvalDesc:
    alias: str
    path_name: str


@dataclass
class SuccessfulSummary:
    file: Path
    theorem_name: str
    search_time: float
    attempts: int


@dataclass
class EvalData:
    alias: str
    results: list[Summary]

    def get_proof_set(self) -> set[ProofPair]:
        return set([ProofPair(str(r.file), r.theorem) for r in self.results])

    def get_successful_searches(self) -> list[SuccessfulSummary]:
        successes: list[SuccessfulSummary] = []
        for r in self.results:
            if r.success:
                assert r.search_time is not None
                match r:
                    case ClassicalSummary():
                        assert r.search_steps is not None
                        num_attempts = r.search_steps
                    case MCTSSummary():
                        assert r.search_time is not None
                        raise ValueError("MCTS does not save number of attempts.")
                    case StraightLineSummary():
                        assert r.attempts is not None
                        num_attempts = len(r.attempts)

                successes.append(
                    SuccessfulSummary(r.file, r.theorem, r.search_time, num_attempts)
                )
        return successes

    def get_time_points(self) -> list[PlotPoint]:
        successes = self.get_successful_searches()
        successes.sort(key=lambda x: x.search_time)
        return [PlotPoint(s.search_time, i + 1) for i, s in enumerate(successes)]

    def get_attempts_points(self) -> list[PlotPoint]:
        successes = self.get_successful_searches()
        successes.sort(key=lambda x: x.attempts)
        return [PlotPoint(s.attempts, i + 1) for i, s in enumerate(successes)]


@dataclass
class ProofPair:
    file_name: str
    theorem_name: str

    def __hash__(self) -> int:
        return hash((self.file_name, self.theorem_name))


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
        [ProofPair(str(s.file), s.theorem_name) for s in e1.get_successful_searches()]
    )
    e2_successes = set(
        [ProofPair(str(s.file), s.theorem_name) for s in e2.get_successful_searches()]
    )
    return TwoEvalSubsets(
        e1_successes - e2_successes,
        e2_successes - e1_successes,
        e1_successes & e2_successes,
    )


def get_three_eval_subets(
    evals: list[EvalData], eval1_alias: str, eval2_alias: str, eval3_alias
) -> ThreeEvalSubsets:
    eval1_list = [e for e in evals if e.alias == eval1_alias]
    assert len(eval1_list) == 1
    eval2_list = [e for e in evals if e.alias == eval2_alias]
    assert len(eval2_list) == 1
    eval3_list = [e for e in evals if e.alias == eval3_alias]
    assert len(eval3_list) == 1

    e1 = eval1_list[0]
    e2 = eval2_list[0]
    e3 = eval3_list[0]
    e1_successes = set(
        [ProofPair(str(s.file), s.theorem_name) for s in e1.get_successful_searches()]
    )
    e2_successes = set(
        [ProofPair(str(s.file), s.theorem_name) for s in e2.get_successful_searches()]
    )
    e3_successes = set(
        [ProofPair(str(s.file), s.theorem_name) for s in e3.get_successful_searches()]
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
            [(s.file, s.theorem_name) for s in e.get_successful_searches()]
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


def find_mutual_proofs(evals: list[EvalData]) -> set[ProofPair]:
    if 0 == len(evals):
        return set()
    inter_proof_set = evals[0].get_proof_set()
    for e in evals[1:]:
        inter_proof_set &= e.get_proof_set()
    return inter_proof_set
