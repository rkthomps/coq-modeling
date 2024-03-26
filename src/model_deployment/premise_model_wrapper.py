from __future__ import annotations
from typing import Iterable, Any, Optional

import sys, os
import json
import requests
import math
import ipdb

from tqdm import tqdm
import torch
from transformers import GPT2Tokenizer
from yaml import load, Loader
from typeguard import typechecked

from coqpyt.coq.structs import TermType

from premise_selection.premise_formatter import (
    PremiseFormat,
    ContextFormat,
    BasicPremiseFormat,
    BasicContextFormat,
    PREMISE_ALIASES,
    CONTEXT_ALIASES,
)
from premise_selection.premise_vector_db import PremiseVectorDB 
from premise_selection.model import PremiseRetriever
from premise_selection.premise_filter import PremiseFilter
from premise_selection.rerank_model import PremiseReranker
from premise_selection.datamodule import tokenize_strings
from premise_selection.rerank_datamodule import collate_examples
from premise_selection.rerank_example import RerankExample
from model_deployment.serve_prem_utils import (
    FORMAT_ENDPOINT,
    PREMISE_ENDPOINT,
    FormatResponse,
    PremiseRequest,
    PremiseResponse,
)
from data_management.dataset_file import DatasetFile, Proof, FocusedStep, Sentence
from data_management.create_premise_dataset import (
    PREMISE_DATA_CONF_NAME,
)

from util.train_utils import get_required_arg
from util.constants import TRAINING_CONF_NAME, RERANK_DATA_CONF_NAME


@typechecked
class RoundRobinCache:
    def __init__(self, max_size: int = 50000) -> None:
        self.cache: dict[str, torch.Tensor] = {}
        self.key_list: list[str] = []
        self.max_size = max_size

    def add(self, key: str, value: torch.Tensor) -> None:
        if key in self.cache:
            return
        if len(self.key_list) == self.max_size:
            removed_key = self.key_list.pop()
            del self.cache[removed_key]
        self.cache[key] = value
        self.key_list.insert(0, key)
        assert len(self.cache) == len(self.key_list)
        assert len(self.key_list) <= self.max_size

    def contains(self, key: str) -> bool:
        return key in self.cache

    def get(self, key: str) -> torch.Tensor:
        return self.cache[key]


@typechecked
class LocalRerankModelWrapper:
    ALIAS = "local-rerank"

    def __init__(
        self,
        reranker: PremiseReranker,
        base_wrapper: PremiseModelWrapper,
        tokenizer: GPT2Tokenizer,
        max_seq_len: int,
        batch_size: int = 32,
        rerank_k: int = 256,
    ) -> None:
        self.reranker = reranker
        self.base_wrapper = base_wrapper
        self.tokenizer = tokenizer
        self.max_seq_len = max_seq_len
        self.batch_size = batch_size
        self.rerank_k = rerank_k
        self.premise_format = self.base_wrapper.premise_format
        self.context_format = self.base_wrapper.context_format
        self.premise_filter = self.base_wrapper.premise_filter

    def batch_examples(self, examples: list[Any]) -> list[list[Any]]:
        batches: list[list[Any]] = []
        cur_batch: list[Any] = []
        for i, example in enumerate(examples):
            if i % self.batch_size == 0 and 0 < len(cur_batch):
                batches.append(cur_batch)
                cur_batch = []
            cur_batch.append(example)
        if 0 < len(cur_batch):
            batches.append(cur_batch)
        return batches

    def rerank(
        self, step: FocusedStep, proof: Proof, premises: list[Sentence]
    ) -> tuple[list[Sentence], list[float]]:
        base_generator = get_ranked_premise_generator(
            self.base_wrapper, step, proof, premises
        )
        top_k: list[Sentence] = []
        rerank_examples: list[RerankExample] = []
        for i, s in enumerate(base_generator):
            if self.rerank_k <= i:
                break
            top_k.append(s)
            formatted_premise = self.base_wrapper.premise_format.format(s)
            formatted_context = self.base_wrapper.context_format.format(step, proof)
            rerank_example = RerankExample(formatted_premise, formatted_context, False)
            rerank_examples.append(rerank_example)
        assert len(top_k) == len(rerank_examples)

        rerank_batches = self.batch_examples(rerank_examples)
        probs: list[float] = []
        with torch.no_grad():
            for batch in rerank_batches:
                collated_batch = collate_examples(
                    batch, self.tokenizer, self.max_seq_len
                )
                batch_outputs = self.reranker(**collated_batch)
                batch_logits = batch_outputs["logits"]
                batch_probs = torch.sigmoid(batch_logits)
                probs.extend(batch_probs.tolist())
        assert len(probs) == len(rerank_examples)

        num_premises = len(rerank_examples)
        arg_sorted_premise_scores = sorted(
            range(num_premises), key=lambda idx: -1 * probs[idx]
        )
        reranked_examples: list[Sentence] = []
        reranked_probs: list[float] = []
        for idx in arg_sorted_premise_scores:
            reranked_examples.append(top_k[idx])
            reranked_probs.append(probs[idx])
        return reranked_examples, reranked_probs

    @classmethod
    def from_checkpoint(cls, checkpoint_loc: str) -> LocalRerankModelWrapper:
        model_loc = os.path.dirname(checkpoint_loc)
        data_preparation_conf = os.path.join(model_loc, RERANK_DATA_CONF_NAME)
        with open(data_preparation_conf, "r") as fin:
            rerank_conf = load(fin, Loader=Loader)
        model_conf_loc = os.path.join(model_loc, TRAINING_CONF_NAME)
        with open(model_conf_loc, "r") as fin:
            model_conf = load(fin, Loader=Loader)
        max_seq_len = get_required_arg("max_seq_len", model_conf)
        tokenizer = GPT2Tokenizer.from_pretrained(model_conf["model_name"])
        base_wrapper = premise_wrapper_from_conf(
            rerank_conf["rerank_formatter"]["premise_wrapper"]
        )
        reranker = PremiseReranker.from_pretrained(checkpoint_loc)
        return cls(reranker, base_wrapper, tokenizer, max_seq_len)


class BM25Okapi:
    ALIAS = "bm25"

    def __init__(self) -> None:
        self.premise_filter = PremiseFilter(
            coq_excludes=[TermType.NOTATION, TermType.TACTIC]
        )
        self.premise_format = BasicPremiseFormat
        self.context_format = BasicContextFormat
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


class TFIdf:
    ALIAS = "tf-idf"

    def __init__(self) -> None:
        self.premise_filter = PremiseFilter(
            coq_excludes=[TermType.NOTATION, TermType.TACTIC]
        )
        self.premise_format = BasicPremiseFormat
        self.context_format = BasicContextFormat

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


@typechecked
class LocalPremiseModelWrapper:
    ALIAS = "local"
    MAX_CACHE_SIZE = 50000

    def __init__(
        self,
        retriever: PremiseRetriever,
        max_seq_len: int,
        tokenizer: GPT2Tokenizer,
        context_format: type[ContextFormat],
        premise_format: type[PremiseFormat],
        premise_filter: PremiseFilter,
        checkpoint_loc: str,
        vector_db: Optional[PremiseVectorDB],
    ) -> None:
        self.retriever = retriever
        self.max_seq_len = max_seq_len
        self.tokenizer = tokenizer
        self.context_format = context_format
        self.premise_format = premise_format
        self.premise_filter = premise_filter
        self.checkpoint_loc = checkpoint_loc
        self.encoding_cache = RoundRobinCache(self.MAX_CACHE_SIZE)
        self.vector_db = vector_db
        self.hits = 0
        self.misses = 0

    def get_input(self, s: str) -> Any:
        inputs = tokenize_strings(self.tokenizer, [s], self.max_seq_len)
        return inputs

    def encode_premise(self, premise: Sentence) -> torch.Tensor:
        if self.vector_db is not None and premise.db_idx is not None:
            embedding = self.vector_db.get(premise.db_idx)
            if embedding is not None:
                return embedding
        premise_str = self.premise_format.format(premise)
        if self.encoding_cache.contains(premise_str):
            self.hits += 1
            return self.encoding_cache.get(premise_str)
        self.misses += 1
        inputs = self.get_input(premise_str)
        with torch.no_grad():
            encoding = self.retriever.encode_premise(
                inputs.input_ids, inputs.attention_mask
            ).to("cpu")
        self.encoding_cache.add(premise_str, encoding)
        return encoding

    def reset_hit_rate(self) -> None:
        self.hits = 0
        self.misses = 0

    def get_hit_rate(self) -> Optional[float]:
        if self.hits + self.misses == 0:
            return None
        return self.hits / (self.hits + self.misses)

    def get_premise_scores_from_strings(
        self, context_str: str, premises: list[Sentence],
    ) -> list[float]:
        if len(premises) == 0:
            return []
        device = self.retriever.device
        context_inputs = self.get_input(context_str)
        with torch.no_grad():
            context_encoding = self.retriever.encode_context(
                context_inputs.input_ids, context_inputs.attention_mask
            ).to(device)
        encodings: list[torch.Tensor] = []
        for premise in premises:
            encoded_premise = self.encode_premise(premise)
            encodings.append(encoded_premise)
        premise_matrix = torch.cat(encodings).to(device)
        similarities = torch.mm(context_encoding, premise_matrix.t())
        ipdb.set_trace()
        assert similarities.shape[0] == 1
        return similarities[0].tolist()

        # similarities.append(
        #     float((context_encoding @ encoded_premise.t()).squeeze())
        # )
        # return similarities
        # premise_encodings.append(encoded_premise)
        # premise_matrix = torch.cat(premise_encodings)
        # similarities = torch.mm(context_encoding, premise_matrix.t())

    def to_json(self) -> Any:
        return {"checkpoint_path", self.checkpoint_loc}

    @classmethod
    def from_json(cls, json_data: Any) -> LocalPremiseModelWrapper:
        checkpoint_loc = json_data["checkpoint_path"]
        return cls.from_checkpoint(checkpoint_loc)

    @classmethod
    def from_checkpoint(cls, checkpoint_loc: str, vector_db_loc: Optional[str]=None) -> LocalPremiseModelWrapper:
        model_loc = os.path.dirname(checkpoint_loc)
        data_preparation_conf = os.path.join(model_loc, PREMISE_DATA_CONF_NAME)
        with open(data_preparation_conf, "r") as fin:
            premise_conf = load(fin, Loader=Loader)
        model_conf_loc = os.path.join(model_loc, TRAINING_CONF_NAME)
        with open(model_conf_loc, "r") as fin:
            model_conf = load(fin, Loader=Loader)
        max_seq_len = get_required_arg("max_seq_len", model_conf)
        tokenizer = GPT2Tokenizer.from_pretrained(model_conf["model_name"])
        premise_format_alias = premise_conf["premise_format_alias"]
        context_format_alias = premise_conf["context_format_alias"]
        premise_format = PREMISE_ALIASES[premise_format_alias]
        context_format = CONTEXT_ALIASES[context_format_alias]
        premise_filter = PremiseFilter.from_json(premise_conf["premise_filter"])
        retriever = PremiseRetriever.from_pretrained(checkpoint_loc)
        if vector_db_loc is not None:
            vector_db = PremiseVectorDB.load(vector_db_loc)
        else:
            vector_db = None
        return cls(
            retriever,
            max_seq_len,
            tokenizer,
            context_format,
            premise_format,
            premise_filter,
            checkpoint_loc,
            vector_db,
        )

    @classmethod
    def from_conf(cls, conf: Any) -> LocalPremiseModelWrapper:
        checkpoint_loc = conf["checkpoint_loc"]
        if "vector_db_loc" in conf:
            vector_db_loc = conf["vector_db_loc"]
        else:
            vector_db_loc = None
        return cls.from_checkpoint(checkpoint_loc, vector_db_loc)


@typechecked
class PremiseServerModelWrapper:
    ALIAS = "server"

    def __init__(
        self,
        url: str,
        context_format: type[ContextFormat],
        premise_format: type[PremiseFormat],
        premise_filter: PremiseFilter,
    ) -> None:
        self.context_format = context_format
        self.premise_format = premise_format
        self.premise_filter = premise_filter
        self.url = url

    def get_premise_scores_from_strings(
        self, context_str: str, premises: list[Sentence]
    ) -> list[float]:
        premise_strs = [self.premise_format.format(p) for p in premises]
        request = PremiseRequest(context_str, premise_strs)
        premise_endpoint = self.url.rstrip("/") + PREMISE_ENDPOINT
        score_response = requests.post(premise_endpoint, request.to_request_data())
        score_data = json.loads(score_response.content)
        score_obj = PremiseResponse.from_json(score_data)
        return score_obj.premise_scores

    @classmethod
    def from_url(cls, url: str) -> PremiseServerModelWrapper:
        format_endpoint = url.rstrip("/") + FORMAT_ENDPOINT
        format_response = requests.post(format_endpoint, {})
        format_data = json.loads(format_response.content)
        format_response_obj = FormatResponse.from_json(format_data)
        context_format = CONTEXT_ALIASES[format_response_obj.context_format_alias]
        premise_format = PREMISE_ALIASES[format_response_obj.preise_format_alias]
        premise_filter = PremiseFilter.from_json(
            format_response_obj.premise_filter_data
        )
        return cls(url, context_format, premise_format, premise_filter)

    @classmethod
    def from_conf(cls, conf: Any) -> PremiseServerModelWrapper:
        return cls.from_url(conf["url"])


PremiseModelWrapper = (
    LocalPremiseModelWrapper
    | PremiseServerModelWrapper
    | LocalRerankModelWrapper
    | TFIdf
    | BM25Okapi
)


def get_premise_scores(
    premise_model: (
        LocalPremiseModelWrapper | PremiseServerModelWrapper | TFIdf | BM25Okapi
    ),
    step: FocusedStep,
    proof: Proof,
    premises: list[Sentence],
) -> list[float]:
    formatted_context = premise_model.context_format.format(step, proof)
    return premise_model.get_premise_scores_from_strings(
        formatted_context, premises 
    )


def get_ranked_premise_generator(
    premise_model: PremiseModelWrapper,
    step: FocusedStep,
    proof: Proof,
    premises: list[Sentence],
) -> Iterable[Sentence]:
    match premise_model:
        case (
            LocalPremiseModelWrapper()
            | PremiseServerModelWrapper()
            | TFIdf()
            | BM25Okapi()
        ):
            premise_scores = get_premise_scores(premise_model, step, proof, premises)
            num_premises = len(premise_scores)
            arg_sorted_premise_scores = sorted(
                range(num_premises), key=lambda idx: -1 * premise_scores[idx]
            )
            for idx in arg_sorted_premise_scores:
                yield premises[idx]
        case LocalRerankModelWrapper():
            ranked_premises, _ = premise_model.rerank(step, proof, premises)
            for rp in ranked_premises:
                yield rp


class PremiseModelNotFound(Exception):
    pass


def move_prem_wrapper_to(
    premise_model_wrapper: PremiseModelWrapper, device: str
) -> None:
    match premise_model_wrapper:
        case LocalPremiseModelWrapper():
            premise_model_wrapper.retriever = premise_model_wrapper.retriever.to(device)
        case LocalRerankModelWrapper():
            premise_model_wrapper.reranker.to(device)
            move_prem_wrapper_to(premise_model_wrapper.base_wrapper, device)
        case _:
            pass


def premise_wrapper_from_conf(conf: Any) -> PremiseModelWrapper:
    attempted_alias = conf["alias"]
    match attempted_alias:
        case LocalPremiseModelWrapper.ALIAS:
            return LocalPremiseModelWrapper.from_conf(conf)
        case PremiseServerModelWrapper.ALIAS:
            return PremiseServerModelWrapper.from_conf(conf)
        case TFIdf.ALIAS:
            return TFIdf()
        case BM25Okapi.ALIAS:
            return BM25Okapi()
        case _:
            raise PremiseModelNotFound(
                f"Could not find premise model wrapper: {attempted_alias}"
            )
