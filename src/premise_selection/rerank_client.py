from __future__ import annotations
from typing import Any, Optional, Iterable

import requests
import random
from dataclasses import dataclass
from pathlib import Path

from data_management.dataset_file import FocusedStep, Proof, DatasetFile, Sentence
from premise_selection.rerank_example import RerankExample
from premise_selection.rerank_formatter import (
    RerankFormatterConf,
    RerankFormatter,
    rerank_formatter_from_conf,
    rerank_conf_from_yaml,
)

from premise_selection.premise_client import (
    SelectClient,
    SelectClientConf,
    SelectModelClientConf,
    SelectPremiseClient,
    select_client_from_conf,
    select_conf_from_yaml,
)

from util.util import FlexibleUrl


@dataclass
class RerankConf:
    ALIAS = "rerank"
    checkpoint_loc: Path
    rerank_num: int
    select_conf: Optional[PremiseConf]

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> RerankConf:
        select_conf = None
        if "select" in yaml_data:
            select_conf = premise_conf_from_yaml(yaml_data["select"])
        return cls(
            Path(yaml_data["checkpoint_loc"]), yaml_data["rerank_num"], select_conf
        )


@dataclass
class RerankClientConf:
    ALIAS = "rerank-client"
    urls: list[FlexibleUrl]
    select_client: PremiseConf
    rerank_num: int
    rerank_formatter: RerankFormatterConf

    def merge(self, other: RerankClientConf) -> RerankClientConf:
        new_urls = self.urls + other.urls
        new_select_client = merge_premise_confs(self.select_client, other.select_client)
        assert self.rerank_num == other.rerank_num
        return RerankClientConf(
            new_urls, new_select_client, self.rerank_num, self.rerank_formatter
        )

    def update_ips(self, port_map: dict[int, tuple[str, int]]):
        for url in self.urls:
            new_ip, new_port = port_map[url.id]
            url.ip = new_ip
            url.port = new_port
        premise_conf_update_ips(self.select_client, port_map)

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> RerankClientConf:
        return cls(
            [FlexibleUrl.from_yaml(u) for u in yaml_data["urls"]],
            premise_conf_from_yaml(yaml_data["select"]),
            yaml_data["rerank_num"],
            rerank_conf_from_yaml(yaml_data["rerank_formatter"]),
        )


PremiseConf = SelectClientConf | RerankConf | RerankClientConf


def premise_conf_update_ips(c: PremiseConf, port_map: dict[int, tuple[str, int]]):
    match c:
        case SelectModelClientConf() | RerankClientConf():
            c.update_ips(port_map)
        case _:
            pass


def merge_premise_confs(conf1: PremiseConf, conf2: PremiseConf) -> PremiseConf:
    match conf1:
        case SelectModelClientConf():
            assert isinstance(conf2, SelectModelClientConf)
            return conf1.merge(conf2)
        case RerankClientConf():
            assert isinstance(conf2, RerankClientConf)
            return conf1.merge(conf2)
        case _:
            assert conf1 == conf2
            return conf1


def premise_conf_from_yaml(yaml_data: Any) -> PremiseConf:
    attempted_alias = yaml_data["alias"]
    match attempted_alias:
        case RerankConf.ALIAS:
            return RerankConf.from_yaml(yaml_data)
        case RerankClientConf.ALIAS:
            return RerankClientConf.from_yaml(yaml_data)
        case _:
            return select_conf_from_yaml(yaml_data)


def premise_client_from_conf(conf: PremiseConf) -> PremiseClient:
    match conf:
        case RerankConf():
            raise ValueError("Rerank Conf CAnnot be directly converted into a client.")
        case RerankClientConf():
            return RerankClient.from_conf(conf)
        case _:
            return select_client_from_conf(conf)


class RerankClient:
    def __init__(
        self,
        urls: list[str],
        select_client: PremiseClient,
        rerank_num: int,
        rerank_formatter: RerankFormatter,
    ):
        self.select_client = select_client
        self.rerank_num = rerank_num
        self.rerank_formatter = rerank_formatter
        self.context_format = self.select_client.context_format
        self.premise_format = self.select_client.premise_format
        self.premise_filter = self.select_client.premise_filter
        self.session = requests.Session()
        self.urls = urls

    def get_scores(self, examples: list[RerankExample]) -> list[float]:
        json_examples = [e.to_json() for e in examples]
        request_data = {
            "method": "get_scores",
            "params": [json_examples],
            "jsonrpc": "2.0",
            "id": 0,
        }
        request_url = random.choice(self.urls)
        response = self.session.post(request_url, json=request_data).json()
        return response["result"]

    def get_ranked_premise_generator(
        self,
        step: FocusedStep,
        proof: Proof,
        dp_obj: DatasetFile,
        premises: list[Sentence],
    ) -> Iterable[Sentence]:
        rerank_premises: list[Sentence] = []
        for premise in self.select_client.get_ranked_premise_generator(
            step, proof, dp_obj, premises
        ):
            rerank_premises.append(premise)
            if self.rerank_num <= len(rerank_premises):
                break
        context_str = self.rerank_formatter.get_formatted_context(step, proof, dp_obj)
        rerank_examples = [
            RerankExample(self.premise_format.format(p), context_str, False)
            for p in rerank_premises
        ]
        rerank_scores = self.get_scores(rerank_examples)
        num_premises = len(rerank_scores)
        arg_sorted_premise_scores = sorted(
            range(num_premises), key=lambda idx: -1 * rerank_scores[idx]
        )
        for idx in arg_sorted_premise_scores:
            yield rerank_premises[idx]

    @classmethod
    def from_conf(cls, conf: RerankClientConf) -> RerankClient:
        return cls(
            [u.get_url() for u in conf.urls],
            premise_client_from_conf(conf.select_client),
            conf.rerank_num,
            rerank_formatter_from_conf(conf.rerank_formatter),
        )


def close_premise_client(c: PremiseClient):
    match c:
        case SelectPremiseClient():
            c.close()
        case _:
            pass


PremiseClient = SelectClient | RerankClient
