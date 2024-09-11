from __future__ import annotations
from typing import Any, Optional
import os
import time
from enum import Enum

import requests
import random
from pathlib import Path
from dataclasses import dataclass
from requests.adapters import Retry, HTTPAdapter

from data_management.dataset_file import Proof, DatasetFile

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
)
from model_deployment.model_result import ModelResult

from proof_retrieval.proof_retriever import (
    ProofRetriever,
    ProofRetrieverConf,
    proof_retriever_conf_from_yaml,
    proof_retriever_from_conf,
    proof_conf_update_ips,
)

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
class DecoderTacticGenConf:
    ALIAS = "decoder"
    checkpoint_loc: Path
    formatter_confs: Optional[list[FormatterConf]]

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> DecoderTacticGenConf:
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

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> LocalTacticGenClientConf:
        return cls(
            [FlexibleUrl.from_yaml(u) for u in yaml_data["urls"]],
            [formatter_conf_from_yaml(f) for f in yaml_data["formatters"]],
        )


class ScoreType(Enum):
    DEPTH = 0
    BREADTH = 1

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> ScoreType:
        match yaml_data:
            case "depth":
                return cls.DEPTH
            case "breadth":
                return cls.BREADTH
            case _:
                raise ValueError(f"Invalid score type", {yaml_data})


@dataclass
class ModelFreeTacticGenClientConf:
    ALIAS = "model_free"
    retriever_conf: ProofRetrieverConf
    score_type: ScoreType

    def update_ips(self, port_map: dict[int, tuple[str, int]]):
        proof_conf_update_ips(self.retriever_conf, port_map)

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> ModelFreeTacticGenClientConf:
        return cls(
            proof_retriever_conf_from_yaml(yaml_data["retriever"]),
            ScoreType.from_yaml(yaml_data["score_type"]),
        )


class ModelFreeTacticGenClient:
    def __init__(self, retriever: ProofRetriever, score_type: ScoreType):
        self.retriever = retriever
        self.score_type = score_type

    def get_recs(
        self, step_idx: int, proof: Proof, dset_file: DatasetFile, n: int, **kwargs: Any
    ) -> ModelResult:
        similar_proof_steps = self.retriever.get_similar_proof_steps(
            step_idx, proof, dset_file, training=False
        )
        similar_tactics: list[str] = []
        scores: list[float] = []
        lengths: list[int] = []

        for proof, step_id in similar_proof_steps:
            similar_tactics.append(proof.steps[step_id.step_idx].step.text)
            match self.score_type:
                case ScoreType.DEPTH:
                    scores.append(1)
                case ScoreType.BREADTH:
                    scores.append(-1)
            lengths.append(1)
            if n <= len(similar_tactics):
                break
            assert len(similar_tactics) == len(scores) == len(lengths)
        return ModelResult(similar_tactics, scores, lengths)

    @classmethod
    def from_conf(cls, conf: ModelFreeTacticGenClientConf) -> ModelFreeTacticGenClient:
        return cls(proof_retriever_from_conf(conf.retriever_conf), conf.score_type)


@dataclass
class PrevProofTacticGenClientConf:
    ALIAS = "prev_proof"
    retriever_conf: ProofRetrieverConf

    def update_ips(self, port_map: dict[int, tuple[str, int]]):
        proof_conf_update_ips(self.retriever_conf, port_map)

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> PrevProofTacticGenClientConf:
        return cls(proof_retriever_conf_from_yaml(yaml_data["retriever"]))


class PrevProofTacticGenClient:
    def __init__(self, retriever: ProofRetriever):
        self.retriever = retriever

    def get_recs(
        self, step_idx: int, proof: Proof, dset_file: DatasetFile, n: int, **kwargs: Any
    ) -> ModelResult:
        similar_proof_steps = self.retriever.get_similar_proof_steps(
            step_idx, proof, dset_file, training=False
        )
        similar_proofs: set[str] = set()
        for proof, _ in similar_proof_steps:
            similar_proofs.add(proof.proof_text_to_string(include_theorem=False))
            if n <= len(similar_proofs):
                break
        return ModelResult(
            list(similar_proofs), [1] * len(similar_proofs), [1] * len(similar_proofs)
        )

    @classmethod
    def from_conf(cls, conf: PrevProofTacticGenClientConf) -> PrevProofTacticGenClient:
        return cls(proof_retriever_from_conf(conf.retriever_conf))


class LocalTacticGenClient:
    def __init__(self, urls: list[str], formatters: list[LmFormatter]) -> None:
        self.formatters = formatters

        self.session = requests.Session()
        # retries = Retry(total=5,
        #                 backoff_factor=0.1,
        #                 status_forcelist=[ 500, 502, 503, 504 ])
        # self.session.mount("http://", HTTPAdapter(max_retries=retries))
        self.urls = urls

    def get_recs(
        self,
        step_idx: int,
        proof: Proof,
        dset_file: DatasetFile,
        n: int,
        beam: bool = False,
        token_mask: Optional[str] = None,
        **kwargs: Any,
    ) -> ModelResult:
        assert 0 < len(self.formatters)
        example = self.formatters[0].example_from_step(
            step_idx, proof.proof_idx, dset_file
        )
        request_id = hash(example)
        request_data = {
            "method": "get_recs",
            "params": [
                example.to_json(),
                n,
                proof.proof_text_to_string(include_theorem=False),
                beam,
                token_mask,
            ],
            "jsonrpc": "2.0",
            "id": request_id,
        }

        chosen_url = random.choice(self.urls)

        start = time.time()
        response = self.session.post(chosen_url, json=request_data).json()
        end = time.time()
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


TacticGenClient = (
    LocalTacticGenClient | ModelFreeTacticGenClient | PrevProofTacticGenClient
)


def tactic_gen_client_from_conf(conf: TacticGenConf) -> TacticGenClient:
    match conf:
        case LocalTacticGenClientConf():
            return LocalTacticGenClient.from_conf(conf)
        case ModelFreeTacticGenClientConf():
            return ModelFreeTacticGenClient.from_conf(conf)
        case PrevProofTacticGenClientConf():
            return PrevProofTacticGenClient.from_conf(conf)
        case _:
            raise ValueError(f"Invalid tactic client config: {str(conf.__class__)}")


def tactic_conf_update_ips(conf: TacticGenConf, port_map: dict[int, tuple[str, int]]):
    match conf:
        case (
            LocalTacticGenClientConf()
            | ModelFreeTacticGenClientConf()
            | PrevProofTacticGenClientConf()
        ):
            conf.update_ips(port_map)
        case _:
            pass


TacticGenConf = (
    LocalTacticGenClientConf
    | ModelFreeTacticGenClientConf
    | PrevProofTacticGenClientConf
    | FidTacticGenConf
    | DecoderTacticGenConf
)


def tactic_gen_conf_from_yaml(yaml_data: Any) -> TacticGenConf:
    attempted_alias = yaml_data["alias"]
    match attempted_alias:
        case LocalTacticGenClientConf.ALIAS:
            return LocalTacticGenClientConf.from_yaml(yaml_data)
        case ModelFreeTacticGenClientConf.ALIAS:
            return ModelFreeTacticGenClientConf.from_yaml(yaml_data)
        case PrevProofTacticGenClientConf.ALIAS:
            return PrevProofTacticGenClientConf.from_yaml(yaml_data)
        case DecoderTacticGenConf.ALIAS:
            return DecoderTacticGenConf.from_yaml(yaml_data)
        case FidTacticGenConf.ALIAS:
            return FidTacticGenConf.from_yaml(yaml_data)
        case _:
            raise ValueError(f"Unknown tactic conf: {attempted_alias}")
