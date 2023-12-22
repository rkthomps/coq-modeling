from __future__ import annotations
from typing import Any

import sys, os
import pdb
import re
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

from proof_selection.torch_data import tokenize_strings, ProofRetBatch


@typechecked
class ProofSelector:
    def __init__(
        self,
        model_name: str,
        lr: float,
        warmup_steps: int,
        max_steps: int,
        max_seq_len: int,
    ):
        self.model_name = model_name
        self.lr = lr
        self.warmup_steps = warmup_steps
        self.max_steps = max_steps
        self.max_seq_len = max_seq_len
        self.device = "cuda"

        self.tokenizer = ByT5Tokenizer.from_pretrained(model_name)
        self.candidate_encoder = T5EncoderModel.from_pretrained(model_name)
        self.context_encoder = T5EncoderModel.from_pretrained(model_name)

    def __encode(
        self, encoder: T5EncoderModel, input_ids: torch.Tensor, mask: torch.Tensor
    ) -> torch.Tensor:
        ## TODO: COULD ADD SOME SORT OF "CPU CHECKPOINTING"
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
        candidate_ids: torch.Tensor,
        candidate_mask: torch.Tensor,
        context_ids: torch.Tensor,
        context_mask: torch.Tensor,
        label: torch.Tensor,
    ) -> torch.Tensor:
        candidate_embs = self.__encode(
            self.candidate_encoder, candidate_ids, candidate_mask
        )
        context_embs = self.__encode(self.context_encoder, context_ids, context_mask)
        similarity = torch.mm(candidate_embs, context_embs.t())
        epsilon = 1e-4
        assert (-1 - epsilon) <= similarity.min() <= similarity.max() <= (1 + epsilon)
        cuda_label = label.to(self.device)
        loss = F.mse_loss(similarity, cuda_label)
        return loss
