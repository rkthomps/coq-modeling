from __future__ import annotations
from typing import Iterable, Any, Optional
import sys, os
import argparse
import re
import functools
from pathlib import Path
import random
import math
import requests
from dataclasses import dataclass

from data_management.dataset_file import Goal
from data_management.sentence_db import SentenceDB
from data_management.dataset_file import FocusedStep, Proof, Sentence
from premise_selection.premise_formatter import (
    ContextFormat,
    PremiseFormat,
    CONTEXT_ALIASES,
    PREMISE_ALIASES,
)
from premise_selection.premise_filter import PremiseFilter, PremiseFilterConf
from coqpyt.coq.structs import TermType


@dataclass
class SelectConf:
    ALIAS = "select"
    checkpoint_loc: Path
    vector_db_loc: Optional[str]

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> SelectConf:
        return cls(Path(yaml_data["checkpoint_loc"]), yaml_data["vector_db_loc"])


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
class TFIdfConf:
    ALIAS = "tfidf"
    context_format_alias: str
    premise_format_alias: str
    premise_filter_conf: PremiseFilterConf

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> TFIdfConf:
        return cls(
            yaml_data["context_format_alias"],
            yaml_data["premise_format_alias"],
            PremiseFilterConf.from_yaml(yaml_data["premise_filter"]),
        )


@dataclass
class BM250OkapiConf:
    ALIAS = "bm25"
    context_format_alias: str
    premise_format_alias: str
    premise_filter_conf: PremiseFilterConf

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> BM250OkapiConf:
        return cls(
            yaml_data["context_format_alias"],
            yaml_data["premise_format_alias"],
            PremiseFilterConf.from_yaml(yaml_data["premise_filter"]),
        )


@dataclass
class LookupClientConf:
    ALIAS = "lookup"
    context_format_alias: str
    premise_format_alias: str
    premise_filter_conf: PremiseFilterConf

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> LookupClientConf:
        return cls(
            yaml_data["context_format_alias"],
            yaml_data["premise_format_alias"],
            PremiseFilterConf.from_yaml(yaml_data["premise_filter"]),
        )


@dataclass
class SelectClientConf:
    ALIAS = "select-client"
    urls: list[str]
    context_format_alias: str
    premise_format_alias: str
    premise_filter_conf: PremiseFilterConf
    sentence_db_loc: Path

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> SelectClientConf:
        return cls(
            yaml_data["urls"],
            yaml_data["context_format_alias"],
            yaml_data["premise_format_alias"],
            PremiseFilterConf.from_yaml(yaml_data["premise_filter"]),
            Path(yaml_data["sentence_db_loc"]),
        )


@dataclass
class RerankClientConf:
    ALIAS = "rerank-client"
    urls: list[str]
    select_client: PremiseConf
    rerank_num: int

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> RerankClientConf:
        return cls(
            yaml_data["urls"],
            premise_conf_from_yaml(yaml_data["select"]),
            yaml_data["rerank_num"],
        )


PremiseConf = (
    SelectConf
    | SelectClientConf
    | RerankConf
    | RerankClientConf
    | TFIdfConf
    | BM250OkapiConf
    | LookupClientConf
)


def premise_conf_from_yaml(yaml_data: Any) -> PremiseConf:
    attempted_alias = yaml_data["alias"]
    match attempted_alias:
        case SelectConf.ALIAS:
            return SelectConf.from_yaml(yaml_data)
        case SelectClientConf.ALIAS:
            return SelectClientConf.from_yaml(yaml_data)
        case RerankConf.ALIAS:
            return RerankConf.from_yaml(yaml_data)
        case RerankClientConf.ALIAS:
            return RerankClientConf.from_yaml(yaml_data)
        case TFIdfConf.ALIAS:
            return TFIdfConf.from_yaml(yaml_data)
        case BM250OkapiConf.ALIAS:
            return BM250OkapiConf.from_yaml(yaml_data)
        case LookupClientConf.ALIAS:
            return LookupClientConf.from_yaml(yaml_data)
        case _:
            raise ValueError("Unknown Configuration")


def premise_client_from_conf(conf: PremiseConf) -> PremiseClient:
    match conf:
        case SelectConf():
            raise ValueError("Select Conf Cannot be directly converted into a client.")
        case SelectClientConf():
            return SelectPremiseClient.from_conf(conf)
        case RerankConf():
            raise ValueError("Rerank Conf CAnnot be directly converted into a client.")
        case RerankClientConf():
            return RerankClient.from_conf(conf)
        case TFIdfConf():
            return TFIdfClient.from_conf(conf)
        case BM250OkapiConf():
            return BM25OkapiClient.from_conf(conf)
        case LookupClientConf():
            return LookupClient.from_conf(conf)


class RerankClient:
    def __init__(self, urls: list[str], select_client: PremiseClient, rerank_num: int):
        self.urls = urls
        self.select_client = select_client
        self.rerank_num = rerank_num
        self.context_format = self.select_client.context_format
        self.premise_format = self.select_client.premise_format
        self.premise_filter = self.select_client.premise_filter

    def get_premise_scores_from_strings(
        self, context_str: str, premises: list[Sentence]
    ) -> list[float]:
        premise_strs = [self.premise_format.format(s) for s in premises]
        request_data = {
            "method": "get_scores",
            "params": [context_str, premise_strs],
            "jsonrpc": "2.0",
            "id": 0,
        }
        request_url = random.choice(self.urls)
        response = requests.post(request_url, json=request_data).json()
        return response["result"]

    def get_ranked_premise_generator(
        self, step: FocusedStep, proof: Proof, premises: list[Sentence]
    ) -> Iterable[Sentence]:
        rerank_premises: list[Sentence] = []
        for premise in self.select_client.get_ranked_premise_generator(
            step, proof, premises
        ):
            rerank_premises.append(premise)
            if self.rerank_num <= len(rerank_premises):
                break
        context_str = self.context_format.format(step, proof)
        rerank_scores = self.get_premise_scores_from_strings(
            context_str, rerank_premises
        )
        num_premises = len(rerank_scores)
        arg_sorted_premise_scores = sorted(
            range(num_premises), key=lambda idx: -1 * rerank_scores[idx]
        )
        for idx in arg_sorted_premise_scores:
            yield rerank_premises[idx]

    @classmethod
    def from_conf(cls, conf: RerankClientConf) -> RerankClient:
        return cls(
            conf.urls, premise_client_from_conf(conf.select_client), conf.rerank_num
        )


class SelectPremiseClient:
    def __init__(
        self,
        urls: list[str],
        context_format: type[ContextFormat],
        premise_format: type[PremiseFormat],
        premise_filter: PremiseFilter,
        sentence_db: SentenceDB,
    ):
        self.urls = urls
        self.context_format = context_format
        self.premise_format = premise_format
        self.premise_filter = premise_filter
        self.sentence_db = sentence_db

    def get_premise_scores_from_strings(
        self, context_str: str, premises: list[Sentence]
    ) -> list[float]:
        idxs: list[int] = []
        orig_idxs: list[int] = []
        orig_idxs_other: list[int] = []
        other_premises: list[Sentence] = []
        for i, p in enumerate(premises):
            if p.db_idx is not None:
                idxs.append(p.db_idx)
                orig_idxs.append(i)
            else:
                other_premises.append(p)
                orig_idxs_other.append(i)

        other_premises_json = [
            s.to_json(self.sentence_db, False) for s in other_premises
        ]
        request_data = {
            "method": "get_scores",
            "params": [context_str, idxs, other_premises_json],
            "jsonrpc": "2.0",
            "id": 0,
        }
        request_url = random.choice(self.urls)
        response = requests.post(request_url, json=request_data).json()

        orig_idxs = orig_idxs + orig_idxs_other
        new_order = sorted(range(len(orig_idxs)), key=lambda idx: orig_idxs[idx])
        scores: list[float] = []
        for new_idx in new_order:
            scores.append(response[new_idx])
        return scores

    def get_ranked_premise_generator(
        self, step: FocusedStep, proof: Proof, premises: list[Sentence]
    ) -> Iterable[Sentence]:
        formatted_context = self.context_format.format(step, proof)
        premise_scores = self.get_premise_scores_from_strings(
            formatted_context, premises
        )
        num_premises = len(premise_scores)
        arg_sorted_premise_scores = sorted(
            range(num_premises), key=lambda idx: -1 * premise_scores[idx]
        )
        for idx in arg_sorted_premise_scores:
            yield premises[idx]

    @classmethod
    def from_conf(cls, conf: SelectClientConf) -> SelectPremiseClient:
        return cls(
            conf.urls,
            CONTEXT_ALIASES[conf.context_format_alias],
            PREMISE_ALIASES[conf.premise_format_alias],
            PremiseFilter.from_conf(conf.premise_filter_conf),
            SentenceDB.load(conf.sentence_db_loc),
        )


@dataclass
class TFIdfClient:
    context_format: type[ContextFormat]
    premise_format: type[PremiseFormat]
    premise_filter: PremiseFilter

    def __clean_token(self, s: str) -> str:
        s = s.lstrip("(,:{")
        s = s.rstrip("),:}")
        return s

    @functools.lru_cache(50000)
    def tokenizer(self, s: str) -> list[str]:
        whitespace_split = s.split()
        clean_tokens: list[str] = []
        for t in whitespace_split:
            clean_t = self.__clean_token(t)
            if 0 < len(clean_t):
                clean_tokens.append(clean_t)
        return clean_tokens

    def compute_idfs(self, corpus: list[str]) -> dict[str, float]:
        if 0 == len(corpus):
            return {}
        assert 0 < len(corpus)
        doc_freqs: dict[str, int] = {}
        for premise in corpus:
            doc = self.tokenizer(premise)
            for word in set(doc):
                if word not in doc_freqs:
                    doc_freqs[word] = 0
                doc_freqs[word] += 1

        idfs: dict[str, float] = {}
        for k, v in doc_freqs.items():
            idfs[k] = math.log(len(corpus) / v)
        return idfs

    @functools.lru_cache(10000)
    def compute_doc_tf(self, premise: str) -> dict[str, float]:
        doc = self.tokenizer(premise)
        if 0 == len(doc):
            return {}
        assert 0 < len(doc)
        term_freqs: dict[str, int] = {}
        for word in doc:
            if word not in term_freqs:
                term_freqs[word] = 0
            term_freqs[word] += 1

        tfs: dict[str, float] = {}
        for k, v in term_freqs.items():
            tfs[k] = v / len(doc)
        return tfs

    def compute_query_tf(self, query: list[str]) -> dict[str, float]:
        if 0 == len(query):
            return {}
        assert 0 < len(query)
        term_freqs: dict[str, int] = {}
        max_term_freq = 0
        for word in query:
            if word not in term_freqs:
                term_freqs[word] = 0
            term_freqs[word] += 1
            if max_term_freq < term_freqs[word]:
                max_term_freq = term_freqs[word]

        tfs: dict[str, float] = {}
        for k, v in term_freqs.items():
            tfs[k] = 0.5 + 0.5 * (v / max_term_freq)
        return tfs

    def get_premise_scores_from_strings(
        self, context_str: str, premises: list[Sentence]
    ) -> list[float]:
        premise_strs = [self.premise_format.format(p) for p in premises]
        query = self.tokenizer(context_str)
        idfs = self.compute_idfs(premise_strs)
        query_tfs = self.compute_query_tf(query)
        doc_tfs = [self.compute_doc_tf(p) for p in premise_strs]
        similarities: list[float] = []
        for doc_tf_dict in doc_tfs:
            dot_prod = 0
            for term, query_tf in query_tfs.items():
                if term not in doc_tf_dict:
                    continue
                if term not in idfs:
                    continue
                query_tf_idf = query_tf * idfs[term]
                doc_tf_idf = doc_tf_dict[term] * idfs[term]
                dot_prod += query_tf_idf * doc_tf_idf
            similarities.append(dot_prod)
        return similarities

    def get_ranked_premise_generator(
        self,
        step: FocusedStep,
        proof: Proof,
        premises: list[Sentence],
    ) -> Iterable[Sentence]:
        formatted_context = self.context_format.format(step, proof)
        premise_scores = self.get_premise_scores_from_strings(
            formatted_context, premises
        )
        num_premises = len(premise_scores)
        arg_sorted_premise_scores = sorted(
            range(num_premises), key=lambda idx: -1 * premise_scores[idx]
        )
        for idx in arg_sorted_premise_scores:
            yield premises[idx]

    @classmethod
    def from_conf(cls, conf: TFIdfConf) -> TFIdfClient:
        return TFIdfClient(
            CONTEXT_ALIASES[conf.context_format_alias],
            PREMISE_ALIASES[conf.premise_format_alias],
            PremiseFilter.from_conf(conf.premise_filter_conf),
        )


@dataclass
class LookupClient:
    context_format: type[ContextFormat]
    premise_format: type[PremiseFormat]
    premise_filter: PremiseFilter
    HYP_PENALTY = 0.7
    COQ_PENALTY = 0.5

    name_forms = [
        re.compile(r"Definition\s+(\S+)[\[\]\{\}\(\):=,\s]"),
        re.compile(r"Fixpoint\s+(\S+)[\[\]\{\}\(\):=,\s]"),
        re.compile(r"CoFixpoint\s+(\S+)[\[\]\{\}\(\):=,\s]"),
        re.compile(r"Inductive\s+(\S+)[\[\]\{\}\(\):=,\s]"),
        re.compile(r"CoInductive\s+(\S+)[\[\]\{\}\(\):=,\s]"),
        re.compile(r"Variant\s+(\S+)[\[\]\{\}\(\):=,\s]"),
        re.compile(r"Class\s+(\S+)[\[\]\{\}\(\):=,\s]"),
        re.compile(r"Module Type\s+(\S+)[\[\]\{\}\(\):=,\s]"),
        re.compile(r"Module\s+(\S+)[\[\]\{\}\(\):=,\s]"),
        re.compile(r"Instance\s+(\S+)[\[\]\{\}\(\):=,\s]"),
    ]

    id_form = re.compile(r"[^\[\]\{\}\(\):=,\s]+")

    def get_ids_from_goal(self, goal: Goal) -> tuple[list[str], list[str]]:
        goal_search_str = goal.goal
        hyp_search_str = ""
        h_ids: set[str] = set()
        for h in goal.hyps:
            h_ty = h.split(":")
            if len(h_ty) == 1:
                hyp_search_str += " " + h_ty[0]
            else:
                h_ids.add(h_ty[0])
                hyp_search_str += " " + "".join(h_ty[1:])
        hyp_found_ids = re.findall(self.id_form, hyp_search_str)
        filtered_hyp_ids = [f for f in hyp_found_ids if f not in h_ids]
        goal_found_ids = re.findall(self.id_form, goal_search_str)
        filtered_goal_ids = [f for f in goal_found_ids if f not in h_ids]
        return filtered_hyp_ids, filtered_goal_ids

    def get_name_from_premise(self, premise: Sentence) -> Optional[str]:
        for name_form in self.name_forms:
            search_match = name_form.search(premise.text)
            if search_match is not None:
                (name,) = search_match.groups()
                return name
        return None

    def get_ranked_premise_generator(
        self,
        step: FocusedStep,
        proof: Proof,
        premises: list[Sentence],
    ) -> Iterable[Sentence]:
        if len(step.goals) == 0:
            empty_premises: list[Sentence] = []
            return empty_premises
        focused_goal = step.goals[0]
        premise_names = [self.get_name_from_premise(p) for p in premises]
        # print(premise_names)
        premise_scores: list[float] = []
        hyp_id_list, goal_id_list = self.get_ids_from_goal(focused_goal)
        hyp_ids = set(hyp_id_list)
        goal_ids = set(goal_id_list)
        for sentence, name in zip(premises, premise_names):
            if name is None:
                premise_scores.append(0)
            elif name in goal_ids:
                from_coq = os.path.join("lib", "coq", "theories") in sentence.file_path
                premise_score = self.COQ_PENALTY if from_coq else 1
                premise_scores.append(premise_score)
            elif name in hyp_ids:
                from_coq = os.path.join("lib", "coq", "theories") in sentence.file_path
                premise_score = (
                    self.COQ_PENALTY * self.HYP_PENALTY
                    if from_coq
                    else self.HYP_PENALTY
                )
                premise_scores.append(premise_score)
            else:
                premise_scores.append(0)

        num_premises = len(premise_scores)
        arg_sorted_premise_scores = sorted(
            range(num_premises), key=lambda idx: -1 * premise_scores[idx]
        )
        for idx in arg_sorted_premise_scores:
            if premise_scores[idx] == 0:
                break
            yield premises[idx]

    @classmethod
    def from_conf(cls, conf: LookupClientConf) -> LookupClient:
        return cls(
            CONTEXT_ALIASES[conf.context_format_alias],
            PREMISE_ALIASES[conf.premise_format_alias],
            PremiseFilter.from_conf(conf.premise_filter_conf),
        )


class BM25OkapiClient:
    def __init__(
        self,
        context_format: type[ContextFormat],
        premise_format: type[PremiseFormat],
        premise_filter: PremiseFilter,
    ):
        self.context_format = context_format
        self.premise_format = premise_format
        self.premise_filter = premise_filter
        self.k1 = 1.8
        self.b = 0.75

    def tokenizer(self, s: str) -> list[str]:
        return s.split()

    def compute_term_freqs(self, doc: list[str]) -> dict[str, int]:
        term_freqs: dict[str, int] = {}
        for term in doc:
            if term not in term_freqs:
                term_freqs[term] = 0
            term_freqs[term] += 1
        return term_freqs

    def compute_doc_freqs(self, corpus: list[list[str]]) -> dict[str, int]:
        doc_freqs: dict[str, int] = {}
        for doc in corpus:
            for word in set(doc):
                if word not in doc_freqs:
                    doc_freqs[word] = 0
                doc_freqs[word] += 1
        return doc_freqs

    def get_premise_scores_from_strings(
        self, context_str: str, premises: list[Sentence]
    ) -> list[float]:
        premise_strs = [self.premise_format.format(p) for p in premises]
        docs = [self.tokenizer(p) for p in premise_strs]
        query = self.tokenizer(context_str)
        doc_freqs = self.compute_doc_freqs(docs)
        avg_doc_len = sum([len(d) for d in docs]) / len(docs)
        doc_term_freqs = [self.compute_term_freqs(doc) for doc in docs]

        similarities: list[float] = []
        for doc, doc_term_dict in zip(docs, doc_term_freqs):
            doc_similarity = 0
            for term in query:
                if term not in doc_freqs:
                    continue
                if term not in doc_term_dict:
                    continue
                query_idf = math.log(
                    (len(docs) - doc_freqs[term] + 0.5) / (doc_freqs[term] + 0.5) + 1
                )
                doc_term_num = doc_term_dict[term] * (self.k1 + 1)
                doc_term_denom = doc_term_dict[term] + self.k1 * (
                    1 - self.b + self.b * len(doc) / avg_doc_len
                )
                doc_similarity += query_idf * doc_term_num / doc_term_denom
            similarities.append(doc_similarity)
        return similarities

    def get_ranked_premise_generator(
        self,
        step: FocusedStep,
        proof: Proof,
        premises: list[Sentence],
    ) -> Iterable[Sentence]:
        formatted_context = self.context_format.format(step, proof)
        premise_scores = self.get_premise_scores_from_strings(
            formatted_context, premises
        )
        num_premises = len(premise_scores)
        arg_sorted_premise_scores = sorted(
            range(num_premises), key=lambda idx: -1 * premise_scores[idx]
        )
        for idx in arg_sorted_premise_scores:
            yield premises[idx]

    @classmethod
    def from_conf(cls, conf: BM250OkapiConf) -> BM25OkapiClient:
        return cls(
            CONTEXT_ALIASES[conf.context_format_alias],
            PREMISE_ALIASES[conf.premise_format_alias],
            PremiseFilter.from_conf(conf.premise_filter_conf),
        )


PremiseClient = (
    SelectPremiseClient | RerankClient | TFIdfClient | BM25OkapiClient | LookupClient
)
