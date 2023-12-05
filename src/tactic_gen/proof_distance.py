from typing import Optional
import logging

from data_management.dataset_file import Proof
from util import util

_logger = util.get_basic_logger(__name__, logging.WARN)

from tactic_gen.tactic_pair_encoding import TacticPairEncoding


def levenshtein_dist_fast(strs1: list[str], strs2: list[str]) -> int:
    scores: list[list[int]] = []
    for i in range(len(strs1) + 1):
        cur_row: list[int] = []
        for j in range(len(strs2) + 1):
            if i == 0:
                cur_row.append(j)
            elif j == 0:
                cur_row.append(i)
            elif strs1[i - 1] == strs2[j - 1]:
                cur_row.append(scores[i - 1][j - 1])
            else:
                cur_row.append(
                    1 + min(scores[i - 1][j - 1], cur_row[j - 1], scores[i - 1][j])
                )
        scores.append(cur_row)
    return scores[len(strs1)][len(strs2)]


ProblemKey = tuple[tuple[str, ...], tuple[str, ...]]


def __get_problem_key(k1: list[str], k2: list[str]) -> ProblemKey:
    return tuple(k1), tuple(k2)


def levenshtein_dist(
    norm_steps1: list[str],
    norm_steps2: list[str],
    subproblems: Optional[dict[ProblemKey, int]] = None,
) -> int:
    if subproblems is None:
        subproblems = {}
    result: Optional[int] = None
    problem_key = __get_problem_key(norm_steps1, norm_steps2)
    if problem_key in subproblems:
        return subproblems[problem_key]

    if len(norm_steps1) == 0:
        result = len(norm_steps2)
    elif len(norm_steps2) == 0:
        result = len(norm_steps1)

    elif norm_steps1[0] == norm_steps2[0]:
        result = levenshtein_dist(norm_steps1[1:], norm_steps2[1:], subproblems)
    else:
        result = 1 + min(
            levenshtein_dist(norm_steps1, norm_steps2[1:], subproblems),
            levenshtein_dist(norm_steps1[1:], norm_steps2, subproblems),
            levenshtein_dist(norm_steps1[1:], norm_steps2[1:], subproblems),
        )

    subproblems[problem_key] = result
    return result


def norm_levenshtein_dist(proof1: Proof, proof2: Proof) -> float:
    try:
        proof1_norm_steps = [
            TacticPairEncoding.normalize_step(s.step.text) for s in proof1.steps
        ]
        proof2_norm_steps = [
            TacticPairEncoding.normalize_step(s.step.text) for s in proof2.steps
        ]
        max_distance = max(len(proof1_norm_steps), len(proof2_norm_steps))
        raw_lev_dist = levenshtein_dist_fast(proof1_norm_steps, proof2_norm_steps)
        return raw_lev_dist / max_distance
    except:
        _logger.warn(
            f"Could not parse proofs. Proof 1 of str length {len(proof1.proof_text_to_string())}, Proof 2 of str length {len(proof2.proof_text_to_string())}"
        )
        return 1
