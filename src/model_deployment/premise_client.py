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

from data_management.dataset_file import Goal, DatasetFile, DPCache
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

from util.util import get_basic_logger, FlexibleUrl


@dataclass
class SelectModelConf:
    ALIAS = "select"
    checkpoint_loc: Path
    vector_db_loc: Optional[Path]

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> SelectModelConf:
        return cls(Path(yaml_data["checkpoint_loc"]), Path(yaml_data["vector_db_loc"]))


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
class SelectModelClientConf:
    ALIAS = "select-client"
    urls: list[FlexibleUrl]
    context_format_alias: str
    premise_format_alias: str
    premise_filter_conf: PremiseFilterConf
    sentence_db_loc: Path

    def merge(self, other: SelectModelClientConf) -> SelectModelClientConf:
        new_urls = self.urls + other.urls
        assert self.context_format_alias == other.context_format_alias
        assert self.premise_format_alias == other.premise_format_alias
        assert self.premise_filter_conf == other.premise_filter_conf
        assert self.sentence_db_loc == other.sentence_db_loc
        return SelectModelClientConf(
            new_urls,
            self.context_format_alias,
            self.premise_format_alias,
            self.premise_filter_conf,
            self.sentence_db_loc,
        )

    def update_ips(self, port_map: dict[int, tuple[str, int]]):
        for url in self.urls:
            new_ip, new_port = port_map[url.id]
            url.ip = new_ip
            url.port = new_port

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> SelectModelClientConf:
        return cls(
            [FlexibleUrl.from_yaml(u) for u in yaml_data["urls"]],
            yaml_data["context_format_alias"],
            yaml_data["premise_format_alias"],
            PremiseFilterConf.from_yaml(yaml_data["premise_filter"]),
            Path(yaml_data["sentence_db_loc"]),
        )


@dataclass
class TextProofRetrieverConf:
    max_examples: int
    data_loc: Path
    sentence_db_loc: Path

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> TextProofRetrieverConf:
        return cls(
            yaml_data["max_examples"],
            Path(yaml_data["data_loc"]),
            Path(yaml_data["sentence_db_loc"]),
        )


@dataclass
class TFIdfProofClientConf:
    ALIAS = "tfidf-proof"
    context_format_alias: str
    premise_format_alias: str
    premise_filter_conf: PremiseFilterConf
    text_proof_retriever_conf: TextProofRetrieverConf
    nucleus_size: int

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> TFIdfProofClientConf:
        return cls(
            yaml_data["context_format_alias"],
            yaml_data["premise_format_alias"],
            PremiseFilterConf.from_yaml(yaml_data["premise_filter"]),
            TextProofRetrieverConf.from_yaml(yaml_data["text_proof_retriever"]),
            yaml_data["nucleus_size"],
        )


ID_FORM = re.compile(r"[^\[\]\{\}\(\):=,\s]+")

SelectClientConf = (
    SelectModelClientConf
    | SelectModelConf
    | TFIdfConf
    | TFIdfProofClientConf
    | BM250OkapiConf
    | LookupClientConf
)


def select_conf_from_yaml(yaml_data: Any) -> SelectClientConf:
    attempted_alias = yaml_data["alias"]
    match attempted_alias:
        case SelectModelConf.ALIAS:
            return SelectModelConf.from_yaml(yaml_data)
        case SelectModelClientConf.ALIAS:
            return SelectModelClientConf.from_yaml(yaml_data)
        case TFIdfConf.ALIAS:
            return TFIdfConf.from_yaml(yaml_data)
        case TFIdfProofClientConf.ALIAS:
            return TFIdfProofClientConf.from_yaml(yaml_data)
        case BM250OkapiConf.ALIAS:
            return BM250OkapiConf.from_yaml(yaml_data)
        case LookupClientConf.ALIAS:
            return LookupClientConf.from_yaml(yaml_data)
        case _:
            raise ValueError("Unknown Configuration")


def get_ids_from_goal(goal: Goal) -> tuple[list[str], list[str]]:
    goal_search_str = goal.goal
    hyp_search_str = ""
    h_ids: set[str] = set()
    for h in goal.hyps:
        h_ty = h.split(":")
        if len(h_ty) == 1:
            hyp_search_str += " " + h_ty[0]
        else:
            h_ids |= set(h_ty[0].split(", "))
            hyp_search_str += " " + "".join(h_ty[1:])
    hyp_found_ids = re.findall(ID_FORM, hyp_search_str)
    filtered_hyp_ids = [f for f in hyp_found_ids if f not in h_ids]
    goal_found_ids = re.findall(ID_FORM, goal_search_str)
    filtered_goal_ids = [f for f in goal_found_ids if f not in h_ids]
    return filtered_hyp_ids, filtered_goal_ids


def get_ids_from_sentence(s: Sentence) -> list[str]:
    sentence_ids = re.findall(ID_FORM, s.text)
    return sentence_ids


class SelectPremiseClient:
    def __init__(
        self,
        urls: list[str],
        context_format: type[ContextFormat],
        premise_format: type[PremiseFormat],
        premise_filter: PremiseFilter,
        sentence_db: SentenceDB,
    ):
        self.context_format = context_format
        self.premise_format = premise_format
        self.premise_filter = premise_filter
        self.sentence_db = sentence_db
        self.session = requests.Session()
        self.urls = urls

    def clear_transformation_matrix(self):
        for url in self.urls:
            request_data = {
                "method": "clear_transform_mat",
                "params": [],
                "jsonrpc": "2.0",
                "id": 0,
            }
            self.session.post(url, json=request_data)

    def set_transformation_matrix(
        self, premises: list[Sentence], steps: list[FocusedStep], proofs: list[Proof]
    ):
        assert len(premises) == len(steps)
        assert len(steps) == len(proofs)
        cstrs = [self.context_format.format(s, p) for s, p in zip(steps, proofs)]
        premises_json = [s.to_json(self.sentence_db, False) for s in premises]
        for url in self.urls:
            request_data = {
                "method": "set_transform_mat",
                "params": [premises_json, cstrs],
                "jsonrpc": "2.0",
                "id": 0,
            }
            self.session.post(url, json=request_data).json()

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
        response = self.session.post(request_url, json=request_data).json()
        result = response["result"]

        orig_idxs = orig_idxs + orig_idxs_other
        new_order = sorted(range(len(orig_idxs)), key=lambda idx: orig_idxs[idx])
        scores: list[float] = []
        for new_idx in new_order:
            scores.append(result[new_idx])
        return scores

    def get_ranked_premise_generator(
        self,
        step: FocusedStep,
        proof: Proof,
        dp_obj: DatasetFile,
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
    def from_conf(cls, conf: SelectModelClientConf) -> SelectPremiseClient:
        return cls(
            [u.get_url() for u in conf.urls],
            CONTEXT_ALIASES[conf.context_format_alias],
            PREMISE_ALIASES[conf.premise_format_alias],
            PremiseFilter.from_conf(conf.premise_filter_conf),
            SentenceDB.load(conf.sentence_db_loc),
        )


def clean_token(s: str) -> str:
    s = s.lstrip("(,:{")
    s = s.rstrip("),:}")
    return s


@functools.lru_cache(50000)
def tokenize(s: str) -> list[str]:
    whitespace_split = s.split()
    clean_tokens: list[str] = []
    for t in whitespace_split:
        clean_t = clean_token(t)
        if 0 < len(clean_t):
            clean_tokens.append(clean_t)
    return clean_tokens


def compute_idfs(corpus: list[list[str]]) -> dict[str, float]:
    if 0 == len(corpus):
        return {}
    assert 0 < len(corpus)
    doc_freqs: dict[str, int] = {}
    for doc in corpus:
        for word in set(doc):
            if word not in doc_freqs:
                doc_freqs[word] = 0
            doc_freqs[word] += 1

    idfs: dict[str, float] = {}
    for k, v in doc_freqs.items():
        idfs[k] = math.log(len(corpus) / v)
    return idfs


def doc_to_hashable(doc: list[str]) -> str:
    return "<DOCSEP>".join(doc)


def doc_from_hashable(s: str) -> list[str]:
    return s.split("<DOCSEP>")


@functools.lru_cache(10000)
def compute_doc_tf(doc_str: str) -> dict[str, float]:
    doc = doc_from_hashable(doc_str)
    # doc = tokenize(premise)
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


def compute_query_tf(query: list[str]) -> dict[str, float]:
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


def tf_idf(
    query: list[str], docs: list[list[str]], idfs: Optional[dict[str, float]] = None
) -> list[float]:
    if idfs is None:
        idfs = compute_idfs(docs)
    query_tfs = compute_query_tf(query)
    doc_tfs = [compute_doc_tf(doc_to_hashable(d)) for d in docs]
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


class TextProofRetriever:
    def __init__(
        self, max_examples: int, data_loc: Path, sentence_db: SentenceDB
    ) -> None:
        self.max_examples = max_examples
        self.data_loc = data_loc
        self.sentence_db = sentence_db
        self.dp_cache = DPCache()

    def get_available_proofs(
        self, key_proof: Proof, dp_obj: DatasetFile
    ) -> list[Proof]:
        available_proofs: list[Proof] = []
        for proof in dp_obj.proofs:
            if proof == key_proof:
                break
            available_proofs.append(proof)

        for dep in dp_obj.dependencies:
            dep_obj = self.dp_cache.get_dp(dep, self.data_loc, self.sentence_db)
            for proof in dep_obj.proofs:
                available_proofs.append(proof)
        return available_proofs

    def get_goal_ids(self, goals: list[Goal]) -> list[str]:
        ids: list[str] = []
        for g in goals:
            hyp_ids, goal_ids = get_ids_from_goal(g)
            ids.extend(hyp_ids)
            ids.extend(goal_ids)
        return ids

    def get_similar_proofs(
        self, key_step: FocusedStep, key_proof: Proof, dp_obj: DatasetFile
    ) -> list[Proof]:
        if len(key_step.goals) == 0:
            return []
        query_ids = self.get_goal_ids(key_step.goals)
        available_proofs = self.get_available_proofs(key_proof, dp_obj)
        reference_proofs: list[Proof] = []
        docs: list[list[str]] = []
        for ref_proof in available_proofs:
            for step in ref_proof.steps:
                reference_proofs.append(ref_proof)
                docs.append(self.get_goal_ids(step.goals))
        assert len(docs) == len(reference_proofs)
        scores = tf_idf(query_ids, docs)
        arg_sorted_scores = sorted(range(len(scores)), key=lambda idx: -1 * scores[idx])
        similar_proofs: list[Proof] = []
        for proof_idx in arg_sorted_scores:
            if self.max_examples <= len(similar_proofs):
                continue
            similar_proof = reference_proofs[proof_idx]
            if similar_proof in similar_proofs:
                continue
            similar_proofs.append(similar_proof)
        return similar_proofs

    def close(self):
        self.sentence_db.close()

    @classmethod
    def from_conf(cls, conf: TextProofRetrieverConf) -> TextProofRetriever:
        return cls(
            conf.max_examples,
            conf.data_loc,
            SentenceDB.load(conf.sentence_db_loc),
        )


class BreakNukeLoop(Exception):
    pass


class TFIdfProofClient:
    def __init__(
        self,
        context_format: type[ContextFormat],
        premise_format: type[PremiseFormat],
        premise_filter: PremiseFilter,
        proof_retriever: TextProofRetriever,
        nucleus_size: int,
    ):
        self.context_format = context_format
        self.premise_format = premise_format
        self.premise_filter = premise_filter
        self.proof_retriever = proof_retriever
        self.nucleus_size = nucleus_size

    def get_ranked_premise_generator(
        self,
        step: FocusedStep,
        proof: Proof,
        dp_obj: DatasetFile,
        premises: list[Sentence],
    ) -> Iterable[Sentence]:
        if 0 == len(step.goals) or 0 == len(premises):
            empty_result: list[Sentence] = []
            return empty_result
        similar_proofs = self.proof_retriever.get_similar_proofs(step, proof, dp_obj)
        # Use the similar proofs to build a nucleus of relevent lemmas
        # How big should the nucleous be?
        nucleus_premises: list[Sentence] = []
        try:
            for s_proof in similar_proofs:
                for s_step in s_proof.steps:
                    for s in s_step.step.context:
                        if self.nucleus_size <= len(nucleus_premises):
                            raise BreakNukeLoop
                        if not self.premise_filter.filter_premise(s):
                            continue
                        if s in nucleus_premises:
                            continue
                        nucleus_premises.append(s)
        except BreakNukeLoop:
            pass

        # Need to normalize tf idf vectors? they're already kind of normalized.
        docs = [get_ids_from_sentence(p) for p in premises]
        idfs = compute_idfs(docs)
        max_scores: Optional[list[float]] = None
        for n in nucleus_premises:
            query = get_ids_from_sentence(n)
            scores = tf_idf(query, docs, idfs)
            if max_scores is None:
                max_scores = scores
            else:
                max_scores = [max(a, b) for a, b in zip(max_scores, scores)]

        if max_scores is None:
            query_hyp_ids, query_goal_ids = get_ids_from_goal(step.goals[0])
            query_ids = query_hyp_ids + query_goal_ids
            max_scores = tf_idf(query_ids, docs, idfs)

        assert max_scores is not None
        arg_sorted_premise_scores = sorted(
            range(len(max_scores)), key=lambda idx: -1 * max_scores[idx]
        )
        for idx in arg_sorted_premise_scores:
            yield premises[idx]

    @classmethod
    def from_conf(cls, conf: TFIdfProofClientConf):
        return cls(
            CONTEXT_ALIASES[conf.context_format_alias],
            PREMISE_ALIASES[conf.premise_format_alias],
            PremiseFilter.from_conf(conf.premise_filter_conf),
            TextProofRetriever.from_conf(conf.text_proof_retriever_conf),
            conf.nucleus_size,
        )


@dataclass
class TFIdfClient:
    context_format: type[ContextFormat]
    premise_format: type[PremiseFormat]
    premise_filter: PremiseFilter

    def get_premise_scores(
        self, context: Goal, premises: list[Sentence]
    ) -> list[float]:
        # premise_strs = [self.premise_format.format(p) for p in premises]
        premise_docs = [get_ids_from_sentence(p) for p in premises]
        query_hyp_ids, query_goal_ids = get_ids_from_goal(context)
        query_ids = query_hyp_ids + query_goal_ids
        # query_ids = query_goal_ids
        # query = tokenize(context_str)
        return tf_idf(query_ids, premise_docs)

    def get_ranked_premise_generator(
        self,
        step: FocusedStep,
        proof: Proof,
        dp_obj: DatasetFile,
        premises: list[Sentence],
    ) -> Iterable[Sentence]:
        if len(step.goals) == 0:
            empty_premises: list[Sentence] = []
            return empty_premises
        focused_goal = step.goals[0]
        # formatted_context = self.context_format.format(step, proof)
        premise_scores = self.get_premise_scores(focused_goal, premises)
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
        re.compile(r"Definition\s+(\S+?)[\[\]\{\}\(\):=,\s]"),
        re.compile(r"Fixpoint\s+(\S+?)[\[\]\{\}\(\):=,\s]"),
        re.compile(r"CoFixpoint\s+(\S+?)[\[\]\{\}\(\):=,\s]"),
        re.compile(r"Inductive\s+(\S+?)[\[\]\{\}\(\):=,\s]"),
        re.compile(r"CoInductive\s+(\S+?)[\[\]\{\}\(\):=,\s]"),
        re.compile(r"Variant\s+(\S+?)[\[\]\{\}\(\):=,\s]"),
        re.compile(r"Class\s+(\S+?)[\[\]\{\}\(\):=,\s]"),
        re.compile(r"Module Type\s+(\S+?)[\[\]\{\}\(\):=,\s]"),
        re.compile(r"Module\s+(\S+?)[\[\]\{\}\(\):=,\s]"),
        re.compile(r"Instance\s+(\S+?)[\[\]\{\}\(\):=,\s]"),
    ]

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
        dp_obj: DatasetFile,
        premises: list[Sentence],
    ) -> Iterable[Sentence]:
        if len(step.goals) == 0:
            empty_premises: list[Sentence] = []
            return empty_premises
        focused_goal = step.goals[0]
        premise_names = [self.get_name_from_premise(p) for p in premises]
        # print(premise_names)
        premise_scores: list[float] = []
        hyp_id_list, goal_id_list = get_ids_from_goal(focused_goal)
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
        dp_obj: DatasetFile,
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


SelectClient = (
    SelectPremiseClient
    | TFIdfClient
    | TFIdfProofClient
    | BM25OkapiClient
    | LookupClient
)


dp_cache = DPCache()


def select_client_from_conf(conf: SelectClientConf) -> SelectClient:
    match conf:
        case SelectModelConf():
            raise ValueError("Select Conf Cannot be directly converted into a client.")
        case SelectModelClientConf():
            return SelectPremiseClient.from_conf(conf)
        case TFIdfConf():
            return TFIdfClient.from_conf(conf)
        case TFIdfProofClientConf():
            return TFIdfProofClient.from_conf(conf)
        case BM250OkapiConf():
            return BM25OkapiClient.from_conf(conf)
        case LookupClientConf():
            return LookupClient.from_conf(conf)


def get_dependency_examples(
    proof_idx: int,
    dset_file: DatasetFile,
    data_loc: Path,
    sentence_db: SentenceDB,
    premise_filter: PremiseFilter,
) -> tuple[list[Sentence], list[FocusedStep], list[Proof]]:
    """To test online learning during premise selection."""
    dep_proofs: list[tuple[Proof, DatasetFile, set[Sentence], set[Sentence]]] = []
    for i, proof in enumerate(dset_file.proofs):
        if proof_idx <= i:
            break
        dep_proofs.append(
            (
                proof,
                dset_file,
                set(dset_file.out_of_file_avail_premises),
                set(dset_file.in_file_avail_premises),
            )
        )

    for dep_name in dset_file.dependencies:
        dep = dp_cache.get_dp(dep_name, data_loc, sentence_db)
        for proof in dep.proofs:
            dep_proofs.append(
                (
                    proof,
                    dep,
                    set(dep.out_of_file_avail_premises),
                    set(dep.in_file_avail_premises),
                )
            )

    learning_premises: list[Sentence] = []
    learning_steps: list[FocusedStep] = []
    learning_proofs: list[Proof] = []
    for proof, dset_file, inf, oof in dep_proofs:
        for step in proof.steps:
            pos_prems = premise_filter.get_pos_filtered_premises(
                step, proof, dset_file, inf, oof
            )
            for p in pos_prems:
                learning_premises.append(p)
                learning_steps.append(step)
                learning_proofs.append(proof)
    return learning_premises, learning_steps, learning_proofs
