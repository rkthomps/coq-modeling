from __future__ import annotations
from typing import Iterable, Any, Optional, TypeVar

import sys, os
from tqdm import tqdm
import torch
from transformers import GPT2Tokenizer
from yaml import load, Loader

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
from data_management.dataset_file import DatasetFile, Proof, FocusedStep, Sentence
from data_management.sentence_db import SentenceDB
from data_management.create_premise_dataset import (
    PREMISE_DATA_CONF_NAME,
)

from util.train_utils import get_required_arg
from util.constants import TRAINING_CONF_NAME, RERANK_DATA_CONF_NAME


T = TypeVar("T")


def batch_examples(exs: list[T], batch_size: int) -> list[list[T]]:
    batches: list[list[Any]] = []
    cur_batch: list[Any] = []
    for e in exs:
        cur_batch.append(e)
        if len(cur_batch) % batch_size == 0:
            batches.append(cur_batch)
            cur_batch = []
    if 0 < len(cur_batch):
        batches.append(cur_batch)
    return batches


class RerankWrapper:
    ALIAS = "local-rerank"

    def __init__(
        self,
        reranker: PremiseReranker,
        tokenizer: GPT2Tokenizer,
        max_seq_len: int,
        batch_size: int = 32,
    ) -> None:
        self.reranker = reranker
        self.tokenizer = tokenizer
        self.max_seq_len = max_seq_len
        self.batch_size = batch_size

    def get_premise_scores(
        self,
        context_str: str,
        premise_strs: list[str],
    ) -> list[float]:
        rerank_examples = [RerankExample(p, context_str, False) for p in premise_strs]
        rerank_batches = batch_examples(rerank_examples, self.batch_size)
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
        return probs

    @classmethod
    def from_checkpoint(cls, checkpoint_loc: str) -> RerankWrapper:
        model_loc = os.path.dirname(checkpoint_loc)
        data_preparation_conf = os.path.join(model_loc, RERANK_DATA_CONF_NAME)
        with open(data_preparation_conf, "r") as fin:
            rerank_conf = load(fin, Loader=Loader)
        model_conf_loc = os.path.join(model_loc, TRAINING_CONF_NAME)
        with open(model_conf_loc, "r") as fin:
            model_conf = load(fin, Loader=Loader)
        max_seq_len = get_required_arg("max_seq_len", model_conf)
        tokenizer = GPT2Tokenizer.from_pretrained(model_conf["model_name"])
        reranker = PremiseReranker.from_pretrained(checkpoint_loc)
        reranker = reranker.to("cuda")
        return cls(reranker, tokenizer, max_seq_len)


class SelectWrapper:
    ALIAS = "local"

    def __init__(
        self,
        retriever: PremiseRetriever,
        max_seq_len: int,
        tokenizer: GPT2Tokenizer,
        premise_format: type[PremiseFormat],
        sentence_db: SentenceDB,
        vector_db: Optional[PremiseVectorDB],
    ) -> None:
        self.retriever = retriever
        self.max_seq_len = max_seq_len
        self.tokenizer = tokenizer
        self.premise_format = premise_format
        self.sentence_db = sentence_db
        self.vector_db = vector_db
        self.batch_size = 128

    def get_input(self, s: str) -> Any:
        inputs = tokenize_strings(self.tokenizer, [s], self.max_seq_len)
        return inputs

    def encode_all(
        self, indices: list[int], non_indices: list[Sentence]
    ) -> torch.Tensor:
        index_sentences: list[Sentence] = []
        for idx in indices:
            s = Sentence.from_idx(idx, self.sentence_db)
            index_sentences.append(s)
        to_encode = index_sentences + non_indices
        to_encode_strs = [self.premise_format.format(s) for s in to_encode]
        return self.get_premise_embs(to_encode_strs)

    def encode_premises(
        self, indices: list[int], non_indices: list[Sentence]
    ) -> torch.Tensor:
        if self.vector_db is not None:
            index_embs = self.vector_db.get_embs(indices)
            if index_embs is None or len(index_embs) == 0:
                return self.encode_all(indices, non_indices)
            to_encode = non_indices
            to_encode_strs = [self.premise_format.format(s) for s in to_encode]
            non_index_embs = self.get_premise_embs(to_encode_strs)
            if len(non_index_embs) == 0:
                return index_embs
            return torch.cat((index_embs, non_index_embs), 0)
        return self.encode_all(indices, non_indices)

    def get_premise_embs(self, premises: list[str]) -> torch.Tensor:
        premise_batches = batch_examples(premises, self.batch_size)
        premise_embs: list[torch.Tensor] = []
        for batch in premise_batches:
            with torch.no_grad():
                batch_inputs = tokenize_strings(
                    self.tokenizer,
                    batch,
                    self.max_seq_len,
                )
                batch_emb = self.retriever.encode_premise(
                    batch_inputs.input_ids, batch_inputs.attention_mask
                )
            premise_embs.append(batch_emb)
        return torch.cat(premise_embs)

    def get_premise_scores(
        self, context_str: str, idx_premises: list[int], other_premises: list[Sentence]
    ) -> list[float]:
        premise_matrix = self.encode_premises(idx_premises, other_premises)
        context_inputs = self.get_input(context_str)
        with torch.no_grad():
            context_encoding = self.retriever.encode_context(
                context_inputs.input_ids, context_inputs.attention_mask
            ).to(self.retriever.device)
        similarities = torch.mm(context_encoding, premise_matrix.t())
        assert similarities.shape[0] == 1
        return similarities[0].tolist()

    @classmethod
    def from_checkpoint(
        cls,
        checkpoint_loc: str,
        vector_db_loc: Optional[str] = None,
    ) -> SelectWrapper:
        model_loc = os.path.dirname(checkpoint_loc)
        data_preparation_conf = os.path.join(model_loc, PREMISE_DATA_CONF_NAME)
        with open(data_preparation_conf, "r") as fin:
            premise_conf = load(fin, Loader=Loader)
        model_conf_loc = os.path.join(model_loc, TRAINING_CONF_NAME)
        with open(model_conf_loc, "r") as fin:
            model_conf = load(fin, Loader=Loader)
        max_seq_len = get_required_arg("max_seq_len", model_conf)
        tokenizer = GPT2Tokenizer.from_pretrained(model_conf["model_name"])
        sentence_db_loc = premise_conf["sentence_db_loc"]
        sentence_db = SentenceDB.load(sentence_db_loc)
        premise_format_alias = premise_conf["premise_format_alias"]
        # context_format_alias = premise_conf["context_format_alias"]
        premise_format = PREMISE_ALIASES[premise_format_alias]
        # context_format = CONTEXT_ALIASES[context_format_alias]
        # premise_filter = PremiseFilter.from_json(premise_conf["premise_filter"])
        retriever = PremiseRetriever.from_pretrained(checkpoint_loc)
        if vector_db_loc is not None:
            vector_db = PremiseVectorDB.load(vector_db_loc)
        else:
            vector_db = None
        return cls(
            retriever,
            max_seq_len,
            tokenizer,
            premise_format,
            sentence_db,
            vector_db,
        )

    @classmethod
    def from_conf(cls, conf: Any) -> SelectWrapper:
        checkpoint_loc = conf["checkpoint_loc"]
        if "vector_db_loc" in conf:
            vector_db_loc = conf["vector_db_loc"]
        else:
            vector_db_loc = None
        return cls.from_checkpoint(checkpoint_loc, vector_db_loc)


# PremiseModelWrapper = (
#     LocalPremiseModelWrapper
#     | PremiseServerModelWrapper
#     | LocalRerankModelWrapper
#     | TFIdf
#     | BM25Okapi
# )


# def get_ranked_premise_generator(
#     premise_model: PremiseModelWrapper,
#     step: FocusedStep,
#     proof: Proof,
#     premises: list[Sentence],
# ) -> Iterable[Sentence]:
#     match premise_model:
#         case (
#             LocalPremiseModelWrapper()
#             | PremiseServerModelWrapper()
#             | TFIdf()
#             | BM25Okapi()
#         ):
#             premise_scores = get_premise_scores(premise_model, step, proof, premises)
#             num_premises = len(premise_scores)
#             arg_sorted_premise_scores = sorted(
#                 range(num_premises), key=lambda idx: -1 * premise_scores[idx]
#             )
#             for idx in arg_sorted_premise_scores:
#                 yield premises[idx]
#         case LocalRerankModelWrapper():
#             ranked_premises, _ = premise_model.rerank(step, proof, premises)
#             for rp in ranked_premises:
#                 yield rp


class PremiseModelNotFound(Exception):
    pass


# def move_prem_wrapper_to(
#     premise_model_wrapper: PremiseModelWrapper, device: str
# ) -> None:
#     match premise_model_wrapper:
#         case LocalPremiseModelWrapper():
#             premise_model_wrapper.retriever = premise_model_wrapper.retriever.to(device)
#             if premise_model_wrapper.vector_db:
#                 premise_model_wrapper.vector_db.device = device
#         case LocalRerankModelWrapper():
#             premise_model_wrapper.reranker.to(device)
#             move_prem_wrapper_to(premise_model_wrapper.base_wrapper, device)
#         case _:
#             pass


# def premise_wrapper_from_conf(conf: Any) -> PremiseModelWrapper:
#     attempted_alias = conf["alias"]
#     match attempted_alias:
#         case LocalPremiseModelWrapper.ALIAS:
#             return LocalPremiseModelWrapper.from_conf(conf)
#         case PremiseServerModelWrapper.ALIAS:
#             return PremiseServerModelWrapper.from_conf(conf)
#         case TFIdf.ALIAS:
#             return TFIdf()
#         case BM25Okapi.ALIAS:
#             return BM25Okapi()
#         case _:
#             raise PremiseModelNotFound(
#                 f"Could not find premise model wrapper: {attempted_alias}"
#             )
