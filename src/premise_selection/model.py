from __future__ import annotations
from typing import Any

import enum
import sys, os
import ipdb
import re
from pytorch_lightning.utilities.types import STEP_OUTPUT, OptimizerLRScheduler
from transformers import (
    ByT5Tokenizer,
    T5EncoderModel,
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
    model_name = "google/byt5-small"

    def __init__(self, **kwargs) -> None:
        super(PremiseRetrieverConfig, self).__init__(**kwargs)


class EncodeType(enum.Enum):
    PREMISE = 1
    CONTEXT = 2


class PremiseRetriever(PreTrainedModel):
    config_class = PremiseRetrieverConfig

    def __init__(self, config: PremiseRetrieverConfig) -> None:
        super(PremiseRetriever, self).__init__(config)
        self.config = config
        self.premise_encoder = T5EncoderModel.from_pretrained(config.model_name)
        self.cxt_encoder = T5EncoderModel.from_pretrained(config.model_name)

    def _encode(
        self, premise: EncodeType, input_ids: torch.Tensor, mask: torch.Tensor
    ) -> torch.Tensor:
        ## TODO: COULD ADD SOME SORT OF "CPU CHECKPOINTING"
        match premise:
            case EncodeType.PREMISE:
                encoder = self.premise_encoder
            case EncodeType.CONTEXT:
                encoder = self.cxt_encoder

        cuda_input_ids = input_ids.to(self.device)
        cuda_mask = mask.to(self.device)
        hidden_states = encoder(
            input_ids=cuda_input_ids,
            attention_mask=cuda_mask,
            return_dict=True,
        ).last_hidden_state
        per_batch_counts = cuda_mask.sum(axis=1)
        masked_hidden_states = hidden_states * cuda_mask[:, :, None]
        summed_hidden_states = masked_hidden_states.sum(axis=1)
        averaged_states = summed_hidden_states / per_batch_counts[:, None]
        return F.normalize(averaged_states, dim=1)

    def forward(
        self,
        context_ids: torch.Tensor,
        context_mask: torch.Tensor,
        premise_ids: torch.Tensor,
        premise_mask: torch.Tensor,
        label: torch.Tensor,
    ) -> dict[str, torch.Tensor]:
        context_embs = self._encode(EncodeType.CONTEXT, context_ids, context_mask)
        premise_embs = self._encode(EncodeType.PREMISE, premise_ids, premise_mask)
        similarity = torch.mm(context_embs, premise_embs.t())
        epsilon = 1e-4
        assert (-1 - epsilon) <= similarity.min() <= similarity.max() <= (1 + epsilon)
        return {"similarities": similarity}

    # @classmethod
    # def fresh(cls, model_name: str) -> PremiseRetrieverSeparate:
    #     encoder = T5EncoderModel.from_pretrained(model_name)
    #     return cls(encoder)

    def encode_str(
        self,
        enc_type: EncodeType,
        to_encode: str,
        tokenizer: ByT5Tokenizer,
        max_seq_len: int,
    ) -> torch.Tensor:
        with torch.no_grad():
            tokens = tokenize_strings(tokenizer, [to_encode], max_seq_len)
            input_ids = tokens.input_ids
            input_masks = tokens.attention_mask
            encoding = self._encode(
                enc_type, input_ids, input_masks
            )  # shape should be 1 x h_dim
            assert encoding.shape[0] == 1
            return encoding
