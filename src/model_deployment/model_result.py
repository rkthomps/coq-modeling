from __future__ import annotations
from typing import Any, Optional


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
        costs: Optional[list[float]] = None,
    ) -> None:
        self.next_tactic_list = next_tactic_list
        self.score_list = score_list
        self.num_tokens_list = num_tokens_list
        self.costs = costs

    def to_json(self) -> Any:
        return {
            "next_tactic_list": self.next_tactic_list,
            "score_list": self.score_list,
            "num_tokens_list": self.num_tokens_list,
            "costs": self.costs,
        }

    def concat(self, mr2: ModelResult) -> ModelResult:
        new = ModelResult(
            self.next_tactic_list + mr2.next_tactic_list,
            self.score_list + mr2.score_list,
            self.num_tokens_list + mr2.num_tokens_list,
            costs=self.costs + mr2.costs if self.costs and mr2.costs else None,
        )
        assert len(new.next_tactic_list) == len(new.score_list)
        assert len(new.next_tactic_list) == len(new.num_tokens_list)
        if new.costs:
            assert len(new.next_tactic_list) == len(new.costs)
        return new

    @classmethod
    def from_json(cls, json_data: Any) -> ModelResult:
        next_tactic_list = json_data["next_tactic_list"]
        score_list = json_data["score_list"]
        num_tokens_list = json_data["num_tokens_list"]
        costs = json_data.get("costs", None)
        return cls(next_tactic_list, score_list, num_tokens_list, costs)

    
    @classmethod
    def empty(cls) -> ModelResult:
        return cls([], [], [], costs=[])
