from __future__ import annotations
from typing import Optional, Type, Any


class ReRankExample:
    def __init__(self, premise: str, context: str, label: bool) -> None:
        self.premise = premise
        self.context = context
        self.label = label

    def to_json(self) -> Any:
        return {
            "premise": self.premise,
            "context": self.context,
            "label": self.label,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> ReRankExample:
        premise = json_data["premise"]
        context = json_data["context"]
        label = json_data["label"]
        return cls(premise, context, label)


class PremiseTrainingExample:
    def __init__(
        self,
        context: str,
        pos_premise: str,
        neg_premises: list[str],
        all_pos_premises: list[str],
    ):
        self.context = context
        self.pos_premise = pos_premise
        self.neg_premises = neg_premises
        self.all_pos_premises = all_pos_premises

    def to_json(self) -> Any:
        return {
            "context": self.context,
            "pos_premise": self.pos_premise,
            "neg_premises": self.neg_premises,
            "all_pos_premises": self.all_pos_premises,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> PremiseTrainingExample:
        context = json_data["context"]
        pos_premise = json_data["pos_premise"]
        neg_premises = json_data["neg_premises"]
        all_pos_premises = json_data["all_pos_premises"]
        return cls(context, pos_premise, neg_premises, all_pos_premises)
