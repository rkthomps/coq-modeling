from typing import Optional
from data_management.dataset_file import Proof

from tactic_gen.tactic_pair_encoding import TacticPairEncoding


__BETWEEN_STEP_SEP = "<|>"


def __get_problem_key(k1: list[str], k2: list[str]) -> tuple[str, str]:
    return __BETWEEN_STEP_SEP.join(k1), __BETWEEN_STEP_SEP.join(k2)


def __levenshtein_dist(
    norm_steps1: list[str],
    norm_steps2: list[str],
    subproblems: dict[tuple[str, str], int],
) -> int:
    result: Optional[int] = None
    problem_key = __get_problem_key(norm_steps1, norm_steps2)
    if problem_key in subproblems:
        return subproblems[problem_key]

    match (norm_steps1, norm_steps2):
        case ([], _):
            result = len(norm_steps2)
        case (_, []):
            result = len(norm_steps1)
        case ([a, *rest1], [b, *rest2]):
            if a == b:
                result = __levenshtein_dist(rest1, rest2, subproblems)
            else:
                result = 1 + min(
                    __levenshtein_dist(norm_steps1, rest2, subproblems),
                    __levenshtein_dist(rest1, norm_steps2, subproblems),
                    __levenshtein_dist(rest1, rest2, subproblems),
                )
        case _:
            raise ValueError("This should never happen. Pyright should know that :(")

    subproblems[problem_key] = result
    return result


def norm_levenshtein_dist(proof1: Proof, proof2: Proof) -> float:
    proof1_norm_steps = [
        TacticPairEncoding.normalize_step(s.step.text) for s in proof1.steps
    ]
    proof2_norm_steps = [
        TacticPairEncoding.normalize_step(s.step.text) for s in proof2.steps
    ]
    max_distance = max(len(proof1_norm_steps), len(proof2_norm_steps))
    raw_lev_dist = __levenshtein_dist(proof1_norm_steps, proof2_norm_steps, {})
    return raw_lev_dist / max_distance


if __name__ == "__main__":
    pass
