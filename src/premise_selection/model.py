from __future__ import annotations
from typing import Any, Optional

import sys, os
import ipdb
import re
from enum import Enum

from transformers import (
    GPT2Tokenizer,
    OPTModel,
    get_cosine_schedule_with_warmup,
    T5ForConditionalGeneration,
)
import torch
import torch.nn.functional as F
from yaml import load, Loader

from typeguard import typechecked

from transformers import PreTrainedModel, PretrainedConfig
from premise_selection.training_types import PremiseBatch
from premise_selection.datamodule import tokenize_strings


class PremiseRetrieverConfig(PretrainedConfig):
    model_type = "premise-retriever"
    model_name = "facebook/opt-125m"

    def __init__(self, **kwargs) -> None:
        super(PremiseRetrieverConfig, self).__init__(**kwargs)


class PremiseRetriever(PreTrainedModel):
    config_class = PremiseRetrieverConfig

    def __init__(self, config: PremiseRetrieverConfig) -> None:
        super(PremiseRetriever, self).__init__(config)
        self.config = config
        tokenzier = GPT2Tokenizer.from_pretrained(config.model_name)
        self.vocab_size = tokenzier.vocab_size
        self.decoder = OPTModel.from_pretrained(config.model_name)
        self.d_model = self.__get_d_model()
        self.premise_projection = torch.nn.Linear(
            self.d_model, self.d_model, device=self.device
        )
        self.premise_recovery = torch.nn.Linear(
            self.d_model, self.vocab_size, device=self.device
        )
        self.context_projection = torch.nn.Linear(
            self.d_model, self.d_model, device=self.device
        )
        self.context_recovery = torch.nn.Linear(
            self.d_model, self.vocab_size, device=self.device
        )

    def __get_d_model(self) -> int:
        return int(
            self.decoder(
                self.decoder.dummy_inputs["input_ids"]
            ).last_hidden_state.shape[-1]
        )

    def _get_avg_embedding(
        self, input_ids: torch.Tensor, mask: torch.Tensor
    ) -> torch.Tensor:
        cuda_input_ids = input_ids.to(self.device)
        cuda_mask = mask.to(self.device)
        hidden_states = self.decoder(
            input_ids=cuda_input_ids,
            attention_mask=cuda_mask,
            return_dict=True,
        ).last_hidden_state
        per_batch_counts = cuda_mask.sum(axis=1)
        masked_hidden_states = hidden_states * cuda_mask[:, :, None]
        summed_hidden_states = masked_hidden_states.sum(axis=1)
        averaged_states = summed_hidden_states / per_batch_counts[:, None]
        return averaged_states

    def encode(
        self,
        input_ids: torch.Tensor,
        mask: torch.Tensor,
        projection: torch.nn.Linear,
        recovery: torch.nn.Linear,
        label: Optional[torch.Tensor] = None,
    ) -> tuple[torch.Tensor, Optional[torch.Tensor]]:
        cuda_input_ids = input_ids.to(self.device)
        cuda_mask = mask.to(self.device)
        hidden_states = self.decoder(
            input_ids=cuda_input_ids,
            attention_mask=cuda_mask,
            return_dict=True,
        ).last_hidden_state
        projected_hidden_states = projection(hidden_states)
        per_batch_counts = cuda_mask.sum(axis=1)
        masked_hidden_states = projected_hidden_states * cuda_mask[:, :, None]
        summed_hidden_states = masked_hidden_states.sum(axis=1)
        averaged_states = summed_hidden_states / per_batch_counts[:, None]
        normed_embedding = F.normalize(averaged_states, dim=1)
        if label is not None:
            recovered_logits = recovery(projected_hidden_states)
        else:
            recovered_logits = None
        return normed_embedding, recovered_logits

    def encode_premise(
        self,
        input_ids: torch.Tensor,
        mask: torch.Tensor,
        label: Optional[torch.Tensor] = None,
    ) -> tuple[torch.Tensor, Optional[torch.Tensor]]:
        return self.encode(
            input_ids, mask, self.premise_projection, self.premise_recovery
        )

    def encode_context(
        self,
        input_ids: torch.Tensor,
        mask: torch.Tensor,
        label: Optional[torch.Tensor] = None,
    ) -> tuple[torch.Tensor, Optional[torch.Tensor]]:
        return self.encode(
            input_ids, mask, self.context_projection, self.context_recovery
        )

    def forward(
        self,
        context_ids: torch.Tensor,
        context_mask: torch.Tensor,
        premise_ids: torch.Tensor,
        premise_mask: torch.Tensor,
        label: Optional[torch.Tensor] = None,
    ) -> dict[str, Any]:
        context_embs, recovered_premise_logits = self.encode_context(
            context_ids, context_mask, label
        )
        premise_embs, recovered_context_logits = self.encode_premise(
            premise_ids, premise_mask, label
        )
        similarity = torch.mm(context_embs, premise_embs.t())
        epsilon = 1e-4
        assert (-1 - epsilon) <= similarity.min() <= similarity.max() <= (1 + epsilon)
        return {
            "similarities": similarity,
            "premise_logits": recovered_premise_logits,
            "context_logits": recovered_context_logits,
        }
