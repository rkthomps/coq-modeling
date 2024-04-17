from __future__ import annotations
from typing import Any


def remove_stop_strings(s: str, stop_strings: list[str]) -> str:
    for stop_str in stop_strings:
        stop_idx = s.find(stop_str)
        if stop_idx > -1:
            return s[:stop_idx]
    return s


def filter_recs(
    next_tactics: list[str],
    next_scores: list[float],
    next_num_tokens: list[int],
    stop_strings: list[str],
) -> ModelResult:
    scores_and_tactics = list(zip(next_scores, next_tactics, next_num_tokens))
    scores_and_tactics.sort(reverse=True)
    final_tactics: list[str] = []
    final_scores: list[float] = []
    final_num_tokens: list[int] = []
    seen_tactics: set[str] = set()
    for score, tactic, num_tokens in scores_and_tactics:
        stripped_tactic = tactic.strip()
        if stripped_tactic in seen_tactics:
            continue
        seen_tactics.add(stripped_tactic)
        final_tactics.append(remove_stop_strings(tactic, stop_strings))
        final_scores.append(score)
        final_num_tokens.append(num_tokens)
    return ModelResult(final_tactics, final_scores, final_num_tokens)


class ModelResult:
    def __init__(
        self,
        next_tactic_list: list[str],
        score_list: list[float],
        num_tokens_list: list[int],
    ) -> None:
        self.next_tactic_list = next_tactic_list
        self.score_list = score_list
        self.num_tokens_list = num_tokens_list

    def to_json(self) -> Any:
        return {
            "next_tactic_list": self.next_tactic_list,
            "score_list": self.score_list,
            "num_tokens_list": self.num_tokens_list,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> ModelResult:
        next_tactic_list = json_data["next_tactic_list"]
        score_list = json_data["score_list"]
        num_tokens_list = json_data["num_tokens_list"]
        return cls(next_tactic_list, score_list, num_tokens_list)
