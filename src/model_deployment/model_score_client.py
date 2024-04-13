from __future__ import annotations
import random
import requests
from typing import Any
from dataclasses import dataclass
from pathlib import Path

from goal_evaluation.goal_example import GoalExample 

@dataclass
class ModelScoreClientConf:
    checkpoint_loc: Path

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> ModelScoreClientConf:
        return cls(yaml_data["checkpoint_loc"])

ModelScoreConf = ModelScoreClientConf
# TODO, Not going to worry about this for now. Seems like a really hard problem.

@dataclass
class ModelScoreClient:
    urls: list[str]

    def get_expected_n_left_and_score(self, example: GoalExample) -> tuple[float, float]:
        request_data = {
            "method": "get_recs",
            "params": [example.to_json()],
            "jsonrpc": "2.0",
            "id": 0,
        }

        chosen_url = random.choice(self.urls)
        response = requests.post(chosen_url, json=request_data).json()
        return response["n_left"], response["score"]

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> ModelScoreClient:
        return cls(yaml_data["urls"])