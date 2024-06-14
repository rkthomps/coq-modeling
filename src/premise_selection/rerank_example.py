from __future__ import annotations
from typing import Any


class RerankExample:
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
    def from_json(cls, json_data: Any) -> RerankExample:
        premise = json_data["premise"]
        context = json_data["context"]
        label = json_data["label"]
        return cls(premise, context, label)
