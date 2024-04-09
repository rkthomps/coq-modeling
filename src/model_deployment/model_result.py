from __future__ import annotations
from typing import Any


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
