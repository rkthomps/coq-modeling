from __future__ import annotations
from typing import Any, Optional, Iterable

import logging
import requests
import random
from dataclasses import dataclass
from pathlib import Path

from data_management.sentence_db import SentenceDB
from data_management.dataset_file import FocusedStep, Proof, DatasetFile, Sentence, DPCache
from premise_selection.rerank_example import RerankExample
from premise_selection.retrieved_premise_db import RetrievedPremiseDB
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
    get_cached_premises,
)

from util.util import FlexibleUrl
from util.constants import RANGO_LOGGER

_logger = logging.getLogger(RANGO_LOGGER)


@dataclass
class RerankConf:
    ALIAS = "rerank"
    checkpoint_loc: Path
    rerank_num: int
    select_conf: Optional[PremiseConf]
    cached_premise_loc: Optional[Path]
    sentence_db_loc: Path

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> RerankConf:
        if "cached_premise_loc" in yaml_data:
            cached_premise_loc = Path(yaml_data["cached_premise_loc"])
        else:
            cached_premise_loc = None

        select_conf = None
        if "select" in yaml_data:
            select_conf = premise_conf_from_yaml(yaml_data["select"])

        return cls(
            Path(yaml_data["checkpoint_loc"]),
            yaml_data["rerank_num"],
            select_conf,
            cached_premise_loc,
            Path(yaml_data["sentence_db_loc"]),
        )

@dataclass
class OracleClientConf:
    ALIAS = "oracle-client"
    base_client: PremiseConf
    purity: float 
    sentence_db_loc: Path
    data_loc: Path

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> OracleClientConf:
        return cls(
            premise_conf_from_yaml(yaml_data["base_client"]),
            yaml_data["purity"],
            Path(yaml_data["sentence_db_loc"]),
            Path(yaml_data["data_loc"]),
        )

@dataclass
class RerankClientConf:
    ALIAS = "rerank-client"
    urls: list[FlexibleUrl]
    select_client: PremiseConf
    rerank_num: int
    rerank_formatter: RerankFormatterConf
    cached_premise_loc: Optional[Path]
    sentence_db_loc: Path

    def update_ips(self, port_map: dict[int, tuple[str, int]]):
        for url in self.urls:
            new_ip, new_port = port_map[url.id]
            url.ip = new_ip
            url.port = new_port
        premise_conf_update_ips(self.select_client, port_map)

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> RerankClientConf:
        if "cached_premise_loc" in yaml_data:
            cached_premise_loc = Path(yaml_data["cached_premise_loc"])
        else:
            cached_premise_loc = None
        return cls(
            [FlexibleUrl.from_yaml(u) for u in yaml_data["urls"]],
            premise_conf_from_yaml(yaml_data["select"]),
            yaml_data["rerank_num"],
            rerank_conf_from_yaml(yaml_data["rerank_formatter"]),
            cached_premise_loc,
            Path(yaml_data["sentence_db_loc"]),
        )


PremiseConf = SelectClientConf | RerankConf | RerankClientConf | OracleClientConf


def premise_conf_update_ips(c: PremiseConf, port_map: dict[int, tuple[str, int]]):
    match c:
        case SelectModelClientConf() | RerankClientConf():
            c.update_ips(port_map)
        case _:
            pass


def premise_conf_from_yaml(yaml_data: Any) -> PremiseConf:
    attempted_alias = yaml_data["alias"]
    match attempted_alias:
        case RerankConf.ALIAS:
            return RerankConf.from_yaml(yaml_data)
        case RerankClientConf.ALIAS:
            return RerankClientConf.from_yaml(yaml_data)
        case OracleClientConf.ALIAS:
            return OracleClientConf.from_yaml(yaml_data)
        case _:
            return select_conf_from_yaml(yaml_data)


def premise_client_from_conf(conf: PremiseConf) -> PremiseClient:
    match conf:
        case RerankConf():
            raise ValueError("Rerank Conf CAnnot be directly converted into a client.")
        case RerankClientConf():
            return RerankClient.from_conf(conf)
        case OracleClientConf():
            return OracleClient.from_conf(conf)
        case _:
            return select_client_from_conf(conf)


class OracleClient:
    def __init__(
        self,
        base_client: PremiseClient,
        purity: float,
        sentence_db: SentenceDB,
        data_loc: Path,
    ):
        self.base_client = base_client
        self.purity = purity 
        self.sentence_db = sentence_db
        self.data_loc = data_loc
        self.dp_cache = DPCache()
        self.context_format = self.base_client.context_format
        self.premise_format = self.base_client.premise_format
        self.premise_filter = self.base_client.premise_filter
    
    def collect_premises(
        self,
        proof: Proof,
    ) -> list[Sentence]:
        premises: list[Sentence] = []
        for step in proof.steps:
            for premise in step.step.context:
                if self.premise_filter.filter_premise(premise) and premise not in premises:
                    premises.append(premise)
        return premises

    
    def get_ranked_premises(
        self,
        step_idx: int,
        proof: Proof,
        dp_obj: DatasetFile,
        premises: list[Sentence],
        training: bool,
    ) -> list[Sentence]:
        orig_dp = self.dp_cache.get_dp(dp_obj.dp_name, self.data_loc, self.sentence_db)
        orig_proof = orig_dp.proofs[proof.proof_idx]
        ground_truth_premises = self.collect_premises(orig_proof) 
        ranked_premises = self.base_client.get_ranked_premises(
            step_idx, proof, dp_obj, premises, training
        )
        neg_premises = [p for p in ranked_premises if p not in ground_truth_premises]

        if len(ranked_premises) == 0:
            final_premises = []
            pos_prems = 0
            neg_prems = 0

        elif self.purity == 0:
            final_premises = neg_premises
            pos_prems = 0
            neg_prems = len(neg_premises)

        elif len(ground_truth_premises) == 0:
            final_premises = []
            pos_prems = 0
            neg_prems = 0 
    
        else:
            target_total = int(len(ground_truth_premises) / self.purity)
            target_num_negs = target_total - len(ground_truth_premises)
            random.shuffle(neg_premises)
            neg_premises = neg_premises[:target_num_negs]
            ranked_premises = ground_truth_premises + neg_premises
            random.shuffle(ranked_premises)
            final_premises = ranked_premises
            pos_prems = len(ground_truth_premises)
            neg_prems = len(neg_premises)

        _logger.info(f"OracleClient (DPName: {dp_obj.dp_name}; Proof: {proof.proof_idx}): Purity {self.purity} requested. Observed purity {pos_prems} / {neg_prems}.")
        return final_premises 
    
    @classmethod
    def from_conf(cls, conf: OracleClientConf) -> OracleClient:
        return cls(
            premise_client_from_conf(conf.base_client),
            conf.purity,
            SentenceDB.load(conf.sentence_db_loc),
            conf.data_loc
        )
    


class RerankClient:
    def __init__(
        self,
        urls: list[str],
        select_client: PremiseClient,
        rerank_num: int,
        rerank_formatter: RerankFormatter,
        cached_premises: Optional[RetrievedPremiseDB],
        sentence_db: SentenceDB,
    ):
        self.select_client = select_client
        self.rerank_num = rerank_num
        self.rerank_formatter = rerank_formatter
        self.context_format = self.select_client.context_format
        self.premise_format = self.select_client.premise_format
        self.premise_filter = self.select_client.premise_filter
        self.session = requests.Session()
        self.urls = urls
        self.cached_premises = cached_premises
        self.sentence_db = sentence_db

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

    def get_ranked_premises(
        self,
        step_idx: int,
        proof: Proof,
        dp_obj: DatasetFile,
        premises: list[Sentence],
        training: bool,
    ) -> list[Sentence]:
        if training:
            cached_scores = get_cached_premises(
                self.cached_premises,
                step_idx,
                proof,
                dp_obj,
                self.sentence_db,
            )
            if cached_scores is not None:
                return cached_scores
        step = proof.steps[step_idx]
        rerank_premises: list[Sentence] = []
        for premise in self.select_client.get_ranked_premises(
            step_idx, proof, dp_obj, premises, training
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
        ranked_premises: list[Sentence] = []
        for idx in arg_sorted_premise_scores:
            ranked_premises.append(rerank_premises[idx])
        return ranked_premises

    @classmethod
    def from_conf(cls, conf: RerankClientConf) -> RerankClient:
        return cls(
            [u.get_url() for u in conf.urls],
            premise_client_from_conf(conf.select_client),
            conf.rerank_num,
            rerank_formatter_from_conf(conf.rerank_formatter),
            (
                RetrievedPremiseDB.load(conf.cached_premise_loc)
                if conf.cached_premise_loc is not None
                else None
            ),
            SentenceDB.load(conf.sentence_db_loc),
        )


def close_premise_client(c: PremiseClient):
    match c:
        case SelectPremiseClient():
            c.close()
        case _:
            pass


PremiseClient = SelectClient | RerankClient | OracleClient
