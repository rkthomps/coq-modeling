from __future__ import annotations
from typing import Any, Optional
import os

import requests
import random
from pathlib import Path
from dataclasses import dataclass

import openai

openai.api_key = os.environ["OPENAI_API_KEY"]
from openai import OpenAI

from tactic_gen.lm_example import (
    LmExample,
    GPTFormatter,
    FormatterConf,
    formatter_conf_from_yaml,
)
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
    formatter_confs: Optional[list[FormatterConf]]

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> FidTacticGenConf:
        formatter_confs = None
        if "formatter" in yaml_data:
            formatter_confs = [
                formatter_conf_from_yaml(f) for f in yaml_data["formatters"]
            ]
        return cls(
            Path(yaml_data["checkpoint_loc"]),
            formatter_confs,
        )


@dataclass
class LocalTacticGenClientConf:
    ALIAS = "client"
    urls: list[str]
    formatter_confs: list[FormatterConf]

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> LocalTacticGenClientConf:
        return cls(
            yaml_data["urls"],
            [formatter_conf_from_yaml(f) for f in yaml_data["formatters"]],
        )


@dataclass
class OpenAiCientConf:
    ALIAS = "openai"
    model_name: str
    formatter_conf: FormatterConf

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> OpenAiCientConf:
        formatter_conf = formatter_conf_from_yaml(yaml_data["formatter"])
        return cls(yaml_data["model_name"], formatter_conf)


class OpenAiClient:
    def __init__(self, model_name: str, formatter: GPTFormatter):
        self.model_name = model_name
        self.client = OpenAI(organization=os.environ["OPENAI_ORG_KEY"])
        self.formatter = formatter

    def get_recs(self, example: LmExample, n: int, current_proof: str) -> ModelResult:
        completion = self.client.chat.completions.create(
            model=self.model_name,
            messages=[
                {"role": "system", "content": self.formatter.SYSTEM_MSG},
                {"role": "user", "content": example.input},
            ],
            n=n,
        )
        messages: list[str] = []
        for choice in completion.choices:
            messages.append(choice.message.content)
        print(messages)
        # messages = [
        #     "Proof.\n  intro n.\n  unfold binomial.\n  destruct n.\n  - simpl. reflexivity.\n  - simpl. reflexivity.\nQed.  ",
        # ]
        return ModelResult(messages, [], [])

    @classmethod
    def from_conf(cls, conf: OpenAiCientConf) -> OpenAiClient:
        formatter = formatter_from_conf(conf.formatter_conf)
        assert isinstance(formatter, GPTFormatter)
        return cls(conf.model_name, formatter)


@dataclass
class LocalTacticGenClient:
    urls: list[str]
    formatters: list[LmFormatter]

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
    def from_conf(cls, conf: LocalTacticGenClientConf) -> TacticGenClient:
        return cls(conf.urls, [formatter_from_conf(f) for f in conf.formatter_confs])


TacticGenClient = LocalTacticGenClient | OpenAiClient


def tactic_gen_client_from_conf(conf: TacticGenConf) -> TacticGenClient:
    match conf:
        case LocalTacticGenClientConf():
            return LocalTacticGenClient.from_conf(conf)
        case OpenAiCientConf():
            return OpenAiClient.from_conf(conf)
        case _:
            raise ValueError(f"Invalid tactic client config: {str(conf.__class__)}")


TacticGenConf = LocalTacticGenClientConf | FidTacticGenConf | OpenAiCientConf


def tactic_gen_conf_from_yaml(yaml_data: Any) -> TacticGenConf:
    attempted_alias = yaml_data["alias"]
    match attempted_alias:
        case LocalTacticGenClientConf.ALIAS:
            return LocalTacticGenClientConf.from_yaml(yaml_data)
        case FidTacticGenConf.ALIAS:
            return FidTacticGenConf.from_yaml(yaml_data)
        case OpenAiCientConf.ALIAS:
            return OpenAiCientConf.from_yaml(yaml_data)
        case _:
            raise ValueError(f"Unknown tactic conf: {attempted_alias}")
