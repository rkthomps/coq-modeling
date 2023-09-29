
from __future__ import annotations
from typing import Any

import json


FORMAT_ENDPOINT = "/formatters"
class FormatResponse:
    def __init__(self, context_format_alias: str, 
                 premise_format_alias: str,
                 premise_filter_data: Any) -> None:
        assert type(context_format_alias) == str
        assert type(premise_format_alias) == str
        self.context_format_alias = context_format_alias
        self.preise_format_alias = premise_format_alias
        self.premise_filter_data = premise_filter_data

    def to_json(self) -> Any:
        return {
            "context_format_alias": self.context_format_alias,
            "premise_format_alias": self.preise_format_alias,
            "premise_filter_data": self.premise_filter_data,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> FormatResponse:
        context_format_alias = json_data["context_format_alias"]
        premise_format_alias = json_data["premise_format_alias"]
        premise_filter_data = json_data["premise_filter_data"]
        return cls(context_format_alias, premise_format_alias, premise_filter_data)


PREMISE_ENDPOINT = "/premise"
class PremiseResponse:
    def __init__(self, premise_scores: list[float]) -> None:
        assert type(premise_scores) == list
        assert(all([float(p) for p in premise_scores]))
        self.premise_scores = premise_scores

    def to_json(self) -> Any:
        return {"premise_scores": self.premise_scores}

    @classmethod
    def from_json(cls, json_data: Any) -> PremiseResponse:
        premise_scores = json_data["premise_scores"]
        return cls(premise_scores)


class PremiseRequest:
    def __init__(self, context: str, premises: list[str]) -> None:
        assert type(context) == str
        assert type(premises) == list
        assert all([type(p) == str for p in premises])
        self.context = context
        self.premises = premises

    def to_json(self) -> Any:
        return {
            "context": self.context,
            "premises": self.premises,
        }

    def to_request_data(self) -> dict[str, str]:
        return {"request-data": json.dumps(self.to_json())}

    @classmethod
    def from_request_data(cls, request_data: dict[str, str]) -> PremiseRequest:
        json_data = json.loads(request_data["request-data"])
        return cls.from_json(json_data)

    @classmethod
    def from_json(cls, json_data: Any) -> PremiseRequest:
        context = json_data["context"]
        premises = json_data["premises"]
        return cls(context, premises)
