from __future__ import annotations
from typing import Iterable, Any, Optional

import sys, os
import json
import requests

import torch
from yaml import load, Loader
from typeguard import typechecked

from coqpyt.coq.structs import TermType

from premise_selection.premise_formatter import (
    PremiseFormat,
    ContextFormat,
    PREMISE_ALIASES,
    CONTEXT_ALIASES,
)
from premise_selection.model import PremiseRetriever
from premise_selection.premise_filter import PremiseFilter
from model_deployment.serve_prem_utils import (
    FORMAT_ENDPOINT,
    PREMISE_ENDPOINT,
    FormatResponse,
    PremiseRequest,
    PremiseResponse,
)
from data_management.dataset_file import DatasetFile, Proof, FocusedStep, Sentence
from data_management.create_premise_dataset import PREMISE_DATA_CONF_NAME


@typechecked
class PremiseModelWrapper:
    def __init__(
        self,
        context_format: type[ContextFormat],
        premise_format: type[PremiseFormat],
        premise_filter: PremiseFilter,
    ) -> None:
        self.context_format = context_format
        self.premise_format = premise_format
        self.premise_filter = premise_filter

    def get_premise_scores(
        self, step: FocusedStep, proof: Proof, premises: list[Sentence]
    ) -> list[float]:
        formatted_context = self.context_format.format(step, proof)
        formatted_premises = [self.premise_format.format(p) for p in premises]
        return self.get_premise_scores_from_strings(
            formatted_context, formatted_premises
        )

    def get_premise_scores_from_strings(
        self, context_str: str, premise_strs: list[str]
    ) -> list[float]:
        raise NotImplementedError

    def get_ranked_premise_generator(
        self, step: FocusedStep, proof: Proof, premises: list[Sentence]
    ) -> Iterable[Sentence]:
        premise_scores = self.get_premise_scores(step, proof, premises)
        num_premises = len(premise_scores)
        arg_sorted_premise_scores = sorted(
            range(num_premises), key=lambda idx: -1 * premise_scores[idx]
        )
        for idx in arg_sorted_premise_scores:
            yield premises[idx]


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
class LocalPremiseModelWrapper(PremiseModelWrapper):
    MAX_CACHE_SIZE = 50000

    def __init__(
        self,
        retriever: PremiseRetriever,
        context_format: type[ContextFormat],
        premise_format: type[PremiseFormat],
        premise_filter: PremiseFilter,
        checkpoint_loc: str,
    ) -> None:
        super(LocalPremiseModelWrapper, self).__init__(
            context_format, premise_format, premise_filter
        )
        self.retriever = retriever
        self.checkpoint_loc = checkpoint_loc
        self.encoding_cache = RoundRobinCache(self.MAX_CACHE_SIZE)
        self.hits = 0
        self.misses = 0

    def __encode_str(self, to_encode: str) -> torch.Tensor:
        if self.encoding_cache.contains(to_encode):
            self.hits += 1
            return self.encoding_cache.get(to_encode)
        self.misses += 1
        encoding = self.retriever.encode_str(to_encode)
        self.encoding_cache.add(to_encode, encoding)
        return encoding

    def reset_hit_rate(self) -> None:
        self.hits = 0
        self.misses = 0

    def get_hit_rate(self) -> Optional[float]:
        if self.hits + self.misses == 0:
            return None
        return self.hits / (self.hits + self.misses)

    def get_premise_scores_from_strings(
        self, context_str: str, premise_strs: list[str]
    ) -> list[float]:
        encoded_context = self.__encode_str(context_str)
        premise_encodings: list[torch.Tensor] = []
        for premise_str in premise_strs:
            encoded_premise = self.__encode_str(premise_str)
            premise_encodings.append(encoded_premise)
        premise_matrix = torch.cat(premise_encodings)
        similarities = torch.mm(encoded_context, premise_matrix.t())
        assert similarities.shape[0] == 1
        return similarities.squeeze().tolist()

    def to_json(self) -> Any:
        return {"checkpoint_path", self.checkpoint_loc}

    @classmethod
    def from_json(cls, json_data: Any) -> LocalPremiseModelWrapper:
        checkpoint_loc = json_data["checkpoint_path"]
        return cls.from_checkpoint(checkpoint_loc)

    @classmethod
    def from_checkpoint(cls, checkpoint_loc: str) -> LocalPremiseModelWrapper:
        model_loc = PremiseRetriever.get_model_loc(checkpoint_loc)
        data_preparation_conf = os.path.join(model_loc, PREMISE_DATA_CONF_NAME)
        with open(data_preparation_conf, "r") as fin:
            premise_conf = load(fin, Loader=Loader)
        premise_format_alias = premise_conf["premise_format_alias"]
        context_format_alias = premise_conf["context_format_alias"]
        premise_format = PREMISE_ALIASES[premise_format_alias]
        context_format = CONTEXT_ALIASES[context_format_alias]
        premise_filter = PremiseFilter.from_json(premise_conf["premise_filter"])
        retriever = PremiseRetriever.load_from_checkpoint_loc(checkpoint_loc)
        return cls(
            retriever, context_format, premise_format, premise_filter, checkpoint_loc
        )


@typechecked
class PremiseServerModelWrapper(PremiseModelWrapper):
    def __init__(
        self,
        url: str,
        context_format: type[ContextFormat],
        premise_format: type[PremiseFormat],
        premise_filter: PremiseFilter,
    ) -> None:
        super(PremiseServerModelWrapper, self).__init__(
            context_format, premise_format, premise_filter
        )
        self.url = url

    def get_premise_scores_from_strings(
        self, context_str: str, premise_strs: list[str]
    ) -> list[float]:
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
