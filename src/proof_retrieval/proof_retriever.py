from __future__ import annotations
from typing import Any, Optional
import functools
from dataclasses import dataclass
import requests
import pickle
from enum import Enum

import os
import random
import heapq
from pathlib import Path

from data_management.sentence_db import SentenceDB
from data_management.splits import FileInfo
from data_management.dataset_file import (
    FocusedStep,
    Proof,
    DatasetFile,
    DPCache,
    Goal,
    StepID,
)
from proof_retrieval.retrieved_proof_db import RetrievedProofDB
from proof_retrieval.proof_idx import ProofIdx
from proof_retrieval.tfidf import tf_idf
from proof_retrieval.bm25 import bm25

from util.util import FlexibleUrl
from util.constants import PROOF_VECTOR_DB_METADATA, RANGO_LOGGER

import logging

_logger = logging.getLogger(RANGO_LOGGER)


class SparseKind(Enum):
    TFIDF = 0
    BM25 = 1

    @classmethod
    def from_str(cls, s: str) -> SparseKind:
        match s:
            case "tfidf":
                return SparseKind.TFIDF
            case "bm25":
                return SparseKind.BM25
            case _:
                raise ValueError(f"Unknown sparse kind: {s}")


def get_steps_from_cache(
    cached_proofs: Optional[RetrievedProofDB],
    dp_cache: DPCache,
    data_loc: Path,
    sentence_db: SentenceDB,
    step_idx: int,
    proof: Proof,
    dp_obj: DatasetFile,
) -> Optional[list[tuple[Proof, StepID]]]:
    if cached_proofs is None:
        return None
    cached_result = cached_proofs.get_steps(step_idx, proof.proof_idx, dp_obj)
    if cached_result is None:
        return None
    return_steps: list[tuple[Proof, StepID]] = []
    for step_id in cached_result:
        ref_dp = dp_cache.get_dp(step_id.file, data_loc, sentence_db)
        return_steps.append((ref_dp.proofs[step_id.proof_idx], step_id))
    return return_steps


@dataclass
class SparseProofRetrieverConf:
    kind: str
    max_examples: int
    data_loc: Path
    sentence_db_loc: Path
    cached_proof_loc: Optional[Path]
    first_step_only: bool
    ALIAS = "sparse"

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> SparseProofRetrieverConf:
        if "cached_proof_loc" in yaml_data:
            cached_proof_loc = Path(yaml_data["cached_proof_loc"])
        else:
            cached_proof_loc = None

        return cls(
            yaml_data["kind"],
            yaml_data["max_examples"],
            Path(yaml_data["data_loc"]),
            Path(yaml_data["sentence_db_loc"]),
            cached_proof_loc,
            yaml_data.get("first_step_only", False),
        )


__logged_deps: set[str] = set()


def get_available_proofs(
    key_proof: Proof,
    dp_obj: DatasetFile,
    dp_cache: DPCache,
    data_loc: Path,
    sentence_db: SentenceDB,
) -> list[tuple[Proof, DatasetFile]]:
    available_proofs: list[tuple[Proof, DatasetFile]] = []
    for proof in dp_obj.proofs:
        if proof == key_proof:
            break
        available_proofs.append((proof, dp_obj))

    # print("Dependencies", dp_obj.dependencies)
    for dep in dp_obj.dependencies:
        try:
            dep_obj = dp_cache.get_dp(dep, data_loc, sentence_db)
        except FileNotFoundError:
            if dep not in __logged_deps:
                _logger.warning(f"Could not find dependency: {dep}")
                __logged_deps.add(dep)
            continue
        for proof in dep_obj.proofs:
            available_proofs.append((proof, dep_obj))
    return available_proofs


class SparseProofRetriever:
    def __init__(
        self,
        kind: SparseKind,
        max_examples: int,
        data_loc: Path,
        sentence_db: SentenceDB,
        cached_proofs: Optional[RetrievedProofDB],
        first_step_only: bool,
    ) -> None:
        self.kind = kind
        self.max_examples = max_examples
        self.data_loc = data_loc
        self.sentence_db = sentence_db
        self.cached_proofs = cached_proofs
        self.first_step_only = first_step_only
        self.dp_cache = DPCache(cache_size=512)

    def get_goal_ids(self, goals: list[Goal]) -> list[str]:
        ids: list[str] = []
        for g in goals:
            hyp_ids, goal_ids = g.get_ids()
            ids.extend(hyp_ids)
            ids.extend(goal_ids)
        return ids

    def get_similar_proof_steps(
        self,
        step_idx: int,
        proof: Proof,
        dp_obj: DatasetFile,
        training: bool,
        **kwargs: Any,
    ) -> list[tuple[Proof, StepID]]:
        if self.first_step_only:
            step_idx = 0
        if training:
            cache_result = get_steps_from_cache(
                self.cached_proofs,
                self.dp_cache,
                self.data_loc,
                self.sentence_db,
                step_idx,
                proof,
                dp_obj,
            )
            if cache_result is not None:
                return cache_result
        key_step = proof.steps[step_idx]
        if len(key_step.goals) == 0:
            return []
        query_ids = self.get_goal_ids(key_step.goals)
        available_proofs = get_available_proofs(
            proof, dp_obj, self.dp_cache, self.data_loc, self.sentence_db
        )
        reference_proofs: list[Proof] = []
        reference_dp_files: list[DatasetFile] = []
        reference_step_idxs: list[int] = []
        docs: list[list[str]] = []
        for ref_proof, ref_dp in available_proofs:
            for s_idx, step in enumerate(ref_proof.steps):
                reference_dp_files.append(ref_dp)
                reference_proofs.append(ref_proof)
                reference_step_idxs.append(s_idx)
                docs.append(self.get_goal_ids(step.goals))
        assert len(docs) == len(reference_proofs)
        match self.kind:
            case SparseKind.TFIDF:
                scores = tf_idf(query_ids, docs)
            case SparseKind.BM25:
                scores = bm25(query_ids, docs)
        arg_sorted_scores = sorted(range(len(scores)), key=lambda idx: -1 * scores[idx])

        references = list(
            zip(reference_proofs, reference_dp_files, reference_step_idxs)
        )
        similar_proof_steps: list[tuple[Proof, StepID]] = []
        distinct_proofs: set[tuple[str, int]] = set()
        for proof_idx in arg_sorted_scores:
            ref_proof, ref_dp, ref_step_idx = references[proof_idx]
            key = (ref_dp.dp_name, ref_proof.proof_idx)
            distinct_proofs.add(key)
            similar_proof_steps.append(
                (ref_proof, StepID(ref_dp.dp_name, ref_proof.proof_idx, ref_step_idx))
            )
            if self.max_examples <= len(distinct_proofs):
                break
        return similar_proof_steps

    def get_similar_proofs(
        self,
        key_step_idx: int,
        key_proof: Proof,
        dp_obj: DatasetFile,
        training: bool,
        **kwargs: Any,
    ) -> list[Proof]:
        similar_proof_steps = self.get_similar_proof_steps(
            key_step_idx, key_proof, dp_obj, training
        )
        similar_proofs: list[Proof] = []
        distinct_proofs: set[tuple[str, int]] = set()
        for proof, step_id in similar_proof_steps:
            if (step_id.file, step_id.proof_idx) in distinct_proofs:
                continue
            distinct_proofs.add((step_id.file, step_id.proof_idx))
            similar_proofs.append(proof)
        return similar_proofs

    @classmethod
    def from_conf(cls, conf: SparseProofRetrieverConf) -> SparseProofRetriever:
        if conf.cached_proof_loc is not None:
            cached_proofs = RetrievedProofDB.load(conf.cached_proof_loc)
        else:
            cached_proofs = None
        return cls(
            SparseKind.from_str(conf.kind),
            conf.max_examples,
            conf.data_loc,
            SentenceDB.load(conf.sentence_db_loc),
            cached_proofs,
            conf.first_step_only,
        )


@dataclass
class DeepProofRetrieverConf:
    ALIAS = "deep"
    model_name: str | Path
    vector_db_loc: Path
    max_seq_len: int
    max_num_proofs: int
    sentence_db_loc: Path
    data_loc: Path
    first_step_only: bool

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> DeepProofRetrieverConf:
        model_name = yaml_data["model_name"]
        if os.path.exists(model_name):
            model_name = Path(model_name)
        vector_db_loc = Path(yaml_data["vector_db_loc"])
        sentence_db_loc = Path(yaml_data["sentence_db_loc"])
        data_loc = Path(yaml_data["data_loc"])
        return cls(
            model_name,
            vector_db_loc,
            yaml_data["max_seq_len"],
            yaml_data["max_num_proofs"],
            sentence_db_loc,
            data_loc,
            yaml_data.get("first_step_only", False),
        )


@dataclass
class DeepProofRetrieverClientConf:
    urls: list[FlexibleUrl]
    vector_db_loc: Path
    sentence_db_loc: Path
    data_loc: Path
    max_num_proofs: int
    first_step_only: bool
    ALIAS = "deep-client"

    def update_ips(self, port_map: dict[int, tuple[str, int]]):
        for url in self.urls:
            new_ip, new_port = port_map[url.id]
            url.ip = new_ip
            url.port = new_port

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> DeepProofRetrieverClientConf:
        raise NotImplementedError()


@dataclass
class ProofDBQuery:
    step_idx: int
    proof: Proof
    dp_name: str

    def format(self) -> str:
        goal_sep = "\n[GOAL]\n"
        goal_strings = [g.to_string() for g in self.proof.steps[self.step_idx].goals]
        return goal_sep.join(goal_strings)


# will need to do proofs + premises but this is good for now
class DeepProofRetrieverClient:
    def __init__(
        self,
        urls: list[str],
        proof_idx: ProofIdx,
        sentence_db: SentenceDB,
        data_loc: Path,
        max_num_proofs: int,
        first_step_only: bool,
    ):
        self.urls = urls
        self.proof_idx = proof_idx
        self.data_loc = data_loc
        self.sentence_db = sentence_db
        self.max_num_proofs = max_num_proofs
        self.first_step_only = first_step_only
        self.dp_cache = DPCache()
        self.session = requests.Session()

    def get_available_proofs(
        self, key_proof: Proof, dp_obj: DatasetFile
    ) -> list[tuple[Proof, DatasetFile]]:
        return get_available_proofs(
            key_proof, dp_obj, self.dp_cache, self.data_loc, self.sentence_db
        )

    def get_similar_proof_steps(
        self,
        step_idx: int,
        proof: Proof,
        dp_obj: DatasetFile,
        training: bool,
        **kwargs: Any,
    ) -> list[tuple[Proof, StepID]]:
        if self.first_step_only:
            step_idx = 0
        hashed_step_idx = self.proof_idx.hash_proof_step(
            step_idx, proof, dp_obj.dp_name
        )
        if self.proof_idx.contains(hashed_step_idx):
            query_step_idx = self.proof_idx.get_idx(hashed_step_idx)
        else:
            query_step_idx = None
        # HARD CODED
        goal_str = ProofDBQuery(step_idx, proof, dp_obj.dp_name).format()
        available_proofs_and_objs = self.get_available_proofs(proof, dp_obj)
        available_proof_idxs: list[int] = []
        available_proof_steps: list[tuple[Proof, StepID]] = []
        for p, dep_obj in available_proofs_and_objs:
            for i, step in enumerate(p.steps):
                try:
                    step_hash = self.proof_idx.hash_proof_step(i, p, dep_obj.dp_name)
                    step_idx = self.proof_idx.get_idx(step_hash)
                    available_proof_idxs.append(step_idx)
                    available_proof_steps.append(
                        (p, StepID(dep_obj.dp_name, p.proof_idx, i))
                    )
                except KeyError:
                    _logger.error(f"Could not find step {i} in {dep_obj.dp_name}")
                    return []

        request_url = random.choice(self.urls)
        request_data = {
            "method": "get_scores",
            "params": [goal_str, available_proof_idxs, query_step_idx],
            "jsonrpc": "2.0",
            "id": 0,
        }
        response = self.session.post(request_url, json=request_data).json()
        scores = response["result"]
        assert len(available_proof_steps) == len(scores)
        similar_proof_steps = sorted(
            range(len(available_proof_steps)), key=lambda idx: -1 * scores[idx]
        )
        similar_steps: list[tuple[Proof, StepID]] = []
        for i in similar_proof_steps:
            similar_steps.append(available_proof_steps[i])
        return similar_steps

    def get_similar_proofs(
        self,
        key_step_idx: int,
        key_proof: Proof,
        dp_obj: DatasetFile,
        training: bool,
        **kwargs: Any,
    ) -> list[Proof]:
        similar_proof_steps = self.get_similar_proof_steps(
            key_step_idx, key_proof, dp_obj, training
        )
        similar_proofs: list[Proof] = []
        seen_proofs: set[str] = set()
        for p, i in similar_proof_steps:
            proof_key = p.proof_text_to_string()
            if proof_key in seen_proofs:
                continue
            seen_proofs.add(proof_key)
            similar_proofs.append(p)
            if self.max_num_proofs <= len(similar_proofs):
                break
        return similar_proofs

    @classmethod
    def from_conf(cls, conf: DeepProofRetrieverClientConf) -> DeepProofRetrieverClient:
        metadata_loc = conf.vector_db_loc / PROOF_VECTOR_DB_METADATA
        with metadata_loc.open("rb") as fin:
            metadata = pickle.load(fin)
        proof_idx = metadata["proof_idx"]
        sentence_db = SentenceDB.load(conf.sentence_db_loc)
        return cls(
            [u.get_url() for u in conf.urls],
            proof_idx,
            sentence_db,
            conf.data_loc,
            conf.max_num_proofs,
            conf.first_step_only,
        )


ProofRetrieverConf = (
    SparseProofRetrieverConf | DeepProofRetrieverClientConf | DeepProofRetrieverConf
)

ProofRetriever = SparseProofRetriever | DeepProofRetrieverClient


def proof_conf_update_ips(c: ProofRetrieverConf, port_map: dict[int, tuple[str, int]]):
    match c:
        case DeepProofRetrieverClientConf():
            c.update_ips(port_map)
        case _:
            pass


def close_proof_retriever(retriever: ProofRetriever):
    match retriever:
        case SparseProofRetriever() | DeepProofRetrieverClient():
            retriever.sentence_db.close()


def proof_retriever_from_conf(conf: ProofRetrieverConf) -> ProofRetriever:
    match conf:
        case SparseProofRetrieverConf():
            return SparseProofRetriever.from_conf(conf)
        case DeepProofRetrieverClientConf():
            return DeepProofRetrieverClient.from_conf(conf)
        case DeepProofRetrieverConf():
            raise ValueError("Cannot directly instantiate deep proof retriever.")


def proof_retriever_conf_from_yaml(yaml_data: Any) -> ProofRetrieverConf:
    attempted_alias = yaml_data["alias"]
    match attempted_alias:
        case SparseProofRetrieverConf.ALIAS:
            return SparseProofRetrieverConf.from_yaml(yaml_data)
        case DeepProofRetrieverClientConf.ALIAS:
            return DeepProofRetrieverClientConf.from_yaml(yaml_data)
        case DeepProofRetrieverConf.ALIAS:
            return DeepProofRetrieverConf.from_yaml(yaml_data)
        case _:
            raise ValueError(f"Proof retriever alias: {attempted_alias} not found.")
