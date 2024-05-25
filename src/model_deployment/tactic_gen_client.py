from __future__ import annotations
from typing import Any, Optional
import os

import requests
import random
from pathlib import Path
from dataclasses import dataclass
from requests.adapters import Retry, HTTPAdapter

import openai

openai.api_key = os.environ["OPENAI_API_KEY"]
from openai import OpenAI

from tactic_gen.lm_example import (
    LmExample,
    FormatterConf,
    formatter_conf_from_yaml,
)
from tactic_gen.lm_example import (
    LmFormatter,
    FormatterConf,
    formatter_update_ips,
    formatter_conf_from_yaml,
    formatter_from_conf,
    merge_formatters,
)
from model_deployment.model_result import ModelResult

from util.util import get_basic_logger, FlexibleUrl

_logger = get_basic_logger(__name__)


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
class CodellamaTacticGenConf:
    ALIAS = "codellama"
    checkpoint_loc: Path
    formatter_confs: Optional[list[FormatterConf]]

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> CodellamaTacticGenConf:
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
    urls: list[FlexibleUrl]
    formatter_confs: list[FormatterConf]

    def update_ips(self, port_map: dict[int, tuple[str, int]]):
        for url in self.urls:
            new_ip, new_port = port_map[url.id]
            url.ip = new_ip
            url.port = new_port
        [formatter_update_ips(f, port_map) for f in self.formatter_confs]

    def merge(self, other: LocalTacticGenClientConf) -> LocalTacticGenClientConf:
        new_urls = self.urls + other.urls
        assert len(self.formatter_confs) == len(other.formatter_confs)
        new_formatter_confs = [
            merge_formatters(f1, f2)
            for f1, f2 in zip(self.formatter_confs, other.formatter_confs)
        ]
        return LocalTacticGenClientConf(new_urls, new_formatter_confs)

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> LocalTacticGenClientConf:
        return cls(
            [FlexibleUrl.from_yaml(u) for u in yaml_data["urls"]],
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
    # TODO include system message in this object. Not fomratter
    def __init__(self, model_name: str, formatter: LmFormatter):
        self.model_name = model_name
        self.client = OpenAI(organization=os.environ["OPENAI_ORG_KEY"])
        self.formatter = formatter
        self.formatters = [formatter]

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
        return cls(conf.model_name, formatter)


class LocalTacticGenClient:
    def __init__(self, urls: list[str], formatters: list[LmFormatter]) -> None:
        self.formatters = formatters

        self.session = requests.Session()
        # retries = Retry(total=5,
        #                 backoff_factor=0.1,
        #                 status_forcelist=[ 500, 502, 503, 504 ])
        # self.session.mount("http://", HTTPAdapter(max_retries=retries))
        self.urls = urls

    def get_recs(self, example: LmExample, n: int, current_proof: str) -> ModelResult:
        request_id = hash(example)
        request_data = {
            "method": "get_recs",
            "params": [example.to_json(), n, current_proof],
            "jsonrpc": "2.0",
            "id": request_id,
        }

        chosen_url = random.choice(self.urls)
        response = self.session.post(chosen_url, json=request_data).json()
        if request_id != request_id:
            _logger.error("ID MISMATCH IN REQUESTS")
        assert response["id"] == request_id
        return ModelResult.from_json(response["result"])

    @classmethod
    def from_conf(cls, conf: LocalTacticGenClientConf) -> TacticGenClient:
        return cls(
            [u.get_url() for u in conf.urls],
            [formatter_from_conf(f) for f in conf.formatter_confs],
        )


TacticGenClient = LocalTacticGenClient | OpenAiClient


def tactic_gen_client_from_conf(conf: TacticGenConf) -> TacticGenClient:
    match conf:
        case LocalTacticGenClientConf():
            return LocalTacticGenClient.from_conf(conf)
        case OpenAiCientConf():
            return OpenAiClient.from_conf(conf)
        case _:
            raise ValueError(f"Invalid tactic client config: {str(conf.__class__)}")


def tactic_conf_update_ips(conf: TacticGenConf, port_map: dict[int, tuple[str, int]]):
    match conf:
        case LocalTacticGenClientConf():
            conf.update_ips(port_map)
        case _:
            pass


TacticGenConf = (
    LocalTacticGenClientConf
    | FidTacticGenConf
    | CodellamaTacticGenConf
    | OpenAiCientConf
)


def merge_tactic_confs(conf1: TacticGenConf, conf2: TacticGenConf) -> TacticGenConf:
    match conf1:
        case LocalTacticGenClientConf():
            assert isinstance(conf2, LocalTacticGenClientConf)
            return conf1.merge(conf2)
        case _:
            assert conf1 == conf2
            return conf1


def tactic_gen_conf_from_yaml(yaml_data: Any) -> TacticGenConf:
    attempted_alias = yaml_data["alias"]
    match attempted_alias:
        case LocalTacticGenClientConf.ALIAS:
            return LocalTacticGenClientConf.from_yaml(yaml_data)
        case CodellamaTacticGenConf.ALIAS:
            return CodellamaTacticGenConf.from_yaml(yaml_data)
        case FidTacticGenConf.ALIAS:
            return FidTacticGenConf.from_yaml(yaml_data)
        case OpenAiCientConf.ALIAS:
            return OpenAiCientConf.from_yaml(yaml_data)
        case _:
            raise ValueError(f"Unknown tactic conf: {attempted_alias}")
