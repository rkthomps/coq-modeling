from typing import Iterable
import sys, os
import argparse
import random
import math
import requests

from data_management.sentence_db import SentenceDB 
from data_management.dataset_file import FocusedStep, Proof, Sentence
from premise_selection.premise_formatter import ContextFormat, PremiseFormat
from premise_selection.premise_filter import PremiseFilter
from premise_selection.premise_vector_db import PremiseVectorDB


class SelectPremiseClient:
    def __init__(
        self,
        urls: list[str],
        context_format: type[ContextFormat],
        premise_format: type[PremiseFormat],
        premise_filter: PremiseFilter,
        sentence_db: SentenceDB
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

        other_premises_json = [s.to_json(self.sentence_db, False) for s in other_premises]
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
        


class TFIdfClient:
    ALIAS = "tfidf"
    def __init__(
        self,
        context_format: type[ContextFormat],
        premise_format: type[PremiseFormat],
        premise_filter: PremiseFilter,
    ):
        self.context_format = context_format
        self.premise_format = premise_format
        self.premise_filter = premise_filter

    def tokenizer(self, s: str) -> list[str]:
        return s.split()

    def compute_idfs(self, corpus: list[list[str]]) -> dict[str, float]:
        assert 0 < len(corpus)
        doc_freqs: dict[str, int] = {}
        for doc in corpus:
            for word in set(doc):
                if word not in doc_freqs:
                    doc_freqs[word] = 0
                doc_freqs[word] += 1

        idfs: dict[str, float] = {}
        for k, v in doc_freqs.items():
            idfs[k] = math.log(v / len(corpus))
        return idfs

    def compute_doc_tf(self, doc: list[str]) -> dict[str, float]:
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
        docs = [self.tokenizer(p) for p in premise_strs]
        query = self.tokenizer(context_str)
        idfs = self.compute_idfs(docs)
        query_tfs = self.compute_query_tf(query)
        doc_tfs = [self.compute_doc_tf(doc) for doc in docs]
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


PremiseClient = (
    RerankPremiseClient | SelectPremiseClient | TFIdfClient | BM25OkapiClient
)
