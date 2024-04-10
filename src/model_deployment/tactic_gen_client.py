from __future__ import annotations
from typing import Any

import requests
import random
from pathlib import Path
from dataclasses import dataclass

from tactic_gen.lm_example import LmExample
from tactic_gen.lm_example import (
    LmFormatter,
    FormatterConf,
    formatter_conf_from_yaml,
    formatter_from_conf,
)
from model_deployment.model_result import ModelResult


@dataclass
class FidTacticGenConf:
    ALIAS = "fid"
    checkpoint_loc: Path

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> FidTacticGenConf:
        return cls(
            Path(yaml_data["checkpoint_loc"]),
        )


@dataclass
class TacticGenClientConf:
    ALIAS = "client"
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

    def get_recs(self, example: LmExample, n: int, current_proof: str) -> ModelResult:
        request_data = {
            "method": "get_recs",
            "params": [example.to_json(), n, current_proof],
            "jsonrpc": "2.0",
            "id": 0,
        }

        chosen_url = random.choice(self.urls)
        response = requests.post(chosen_url, json=request_data).json()
        return ModelResult.from_json(response["result"])

    @classmethod
    def from_conf(cls, conf: TacticGenConf) -> TacticGenClient:
        match conf:
            case TacticGenClientConf():
                return cls(conf.urls, formatter_from_conf(conf.formatter_conf))
            case _:
                raise ValueError(
                    f"Cannot produce tactic gen client from {conf.__class__}"
                )


TacticGenConf = TacticGenClientConf | FidTacticGenConf


def tactic_gen_conf_from_yaml(yaml_data: Any) -> TacticGenConf:
    attempted_alias = yaml_data["alias"]
    match attempted_alias:
        case TacticGenClientConf.ALIAS:
            return TacticGenClientConf.from_yaml(yaml_data)
        case FidTacticGenConf.ALIAS:
            return FidTacticGenConf.from_yaml(yaml_data)
        case _:
            raise ValueError(f"Unknown tactic conf: {attempted_alias}")
