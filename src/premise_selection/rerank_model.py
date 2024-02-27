from __future__ import annotations
from typing import Any

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
from torch import nn
from yaml import load, Loader

from typeguard import typechecked

from transformers import PreTrainedModel, PretrainedConfig
from premise_selection.training_types import PremiseBatch
from premise_selection.datamodule import tokenize_strings


class PremiseRerankerConfig(PretrainedConfig):
    model_type = "premise-retriever"
    model_name = "google/byt5-small"

    def __init__(self, **kwargs) -> None:
        super(PremiseRerankerConfig, self).__init__(**kwargs)


class PremiseReranker(PreTrainedModel):
    config_class = PremiseRerankerConfig

    def __init__(self, config: PremiseRerankerConfig) -> None:
        super(PremiseReranker, self).__init__(config)
        self.config = config
        self.encoder = T5EncoderModel.from_pretrained(config.model_name)
        self.d_model = self.__get_d_model()
        self.final_projection = nn.Linear(self.d_model, 1, device=self.device)

    def __get_d_model(self) -> int:
        return int(
            self.encoder(
                self.encoder.dummy_inputs["input_ids"]
            ).last_hidden_state.shape[-1]
        )

    def forward(
        self,
        input_ids: torch.Tensor,
        mask: torch.Tensor,
        labels: torch.Tensor,
    ) -> dict[str, torch.Tensor]:
        cuda_input_ids = input_ids.to(self.device)
        cuda_mask = mask.to(self.device)
        hidden_states = self.encoder(
            input_ids=cuda_input_ids,
            attention_mask=cuda_mask,
            return_dict=True,
        ).last_hidden_state
        per_batch_counts = cuda_mask.sum(axis=1)
        masked_hidden_states = hidden_states * cuda_mask[:, :, None]
        summed_hidden_states = masked_hidden_states.sum(axis=1)
        averaged_states = summed_hidden_states / per_batch_counts[:, None]
        # final_probs = torch.sigmoid(self.final_projection(averaged_states))[:, 0]
        final_logits = self.final_projection(averaged_states)[:, 0]
        return {"logits": final_logits}

    @classmethod
    def fresh(cls, model_name: str) -> PremiseReranker:
        encoder = T5EncoderModel.from_pretrained(model_name)
        return cls(encoder)
