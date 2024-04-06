from __future__ import annotations
from typing import Any

import requests
import random
from pathlib import Path
from dataclasses import dataclass

from tactic_gen.lm_example import LmExample 
from tactic_gen.lm_example import LmFormatter, FormatterConf, formatter_conf_from_yaml, formatter_from_conf
from model_deployment.model_result import ModelResult

@dataclass
class FidTacticGenConf:
    checkpoint_loc: Path

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> FidTacticGenConf:
        return cls(
            Path(yaml_data["checkpoint_loc"]),
        )

@dataclass
class TacticGenClientConf:
    urls: list[str]
    formatter_conf: FormatterConf 

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> TacticGenClientConf:
        return cls(
            yaml_data["urls"],
            formatter_conf_from_yaml(yaml_data["formatter"]),
        )

@dataclass
class TacticGenClient:
    urls: list[str]
    formatter: LmFormatter
    
    def get_recs(self, example: LmExample, n: int) -> ModelResult:
        request_data = {
            "method": "get_recs",
            "params": [example.to_json(), n],
            "jsonrpc": "2.0",
            "id": 0, 
        }

        chosen_url = random.choice(self.urls)
        response = requests.post(chosen_url, json=request_data).json()
        return ModelResult.from_json(response)
    
    @classmethod
    def from_conf(cls, conf: TacticGenClientConf) -> TacticGenClient:
        return cls(
            conf.urls,
            formatter_from_conf(conf.formatter_conf),
        )
        

TacticGenConf = TacticGenClientConf | FidTacticGenConf 

