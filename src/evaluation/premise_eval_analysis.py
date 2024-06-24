import sys, os
import pickle
from pathlib import Path
from dataclasses import dataclass

from evaluation.eval_utils import PremiseProofResult, PremiseStepResult


@dataclass
class EvalDesc:
    alias: str
    path_name: str


@dataclass
class VerboseStepResult:
    file: str
    proof_idx: int
    step_idx: int
    num_premises: int
    hits_on: list[int]

    def hit_by_k(self, k: int) -> bool:
        filtered_hits_on = [h for h in self.hits_on if h <= k]
        return len(filtered_hits_on) == self.num_premises


@dataclass
class PremiseEvalData:
    alias: str
    proof_results: list[VerboseStepResult]

    def recall_at_k(self, k: int) -> float:
        return sum([r.hit_by_k(k) for r in self.proof_results]) / len(
            self.proof_results
        )

    def overall_recall_at_k(self, k: int) -> float:
        num_prems = 0
        num_prems_hit = 0
        for r in self.proof_results:
            hits_below_k = [h for h in r.hits_on if h <= k]
            num_prems_hit += len(hits_below_k)
            num_prems += r.num_premises
        return num_prems_hit / num_prems


def load_pkl_results(results_loc: Path) -> list[PremiseProofResult]:
    results: list[PremiseProofResult] = []
    for f in os.listdir(results_loc):
        if f.endswith(".pkl"):
            with open(results_loc / f, "rb") as fin:
                result = pickle.load(fin)
                results.append(result)
    return results


def flatten_proof_result(result: PremiseProofResult) -> list[VerboseStepResult]:
    return [
        VerboseStepResult(
            result.file,
            result.proof_idx,
            s.step_idx,
            s.num_premises,
            s.hits_on,
        )
        for s in result.step_results
    ]


def load_evals(eval_descs: list[EvalDesc], results_loc: Path) -> list[PremiseEvalData]:
    evals: list[PremiseEvalData] = []
    for eval_desc in eval_descs:
        e_proof_results = load_pkl_results(results_loc / eval_desc.path_name)
        e_total_results: list[VerboseStepResult] = []
        for p in e_proof_results:
            e_total_results.extend(flatten_proof_result(p))
        eval_data = PremiseEvalData(eval_desc.alias, e_total_results)
        evals.append(eval_data)
    return evals
