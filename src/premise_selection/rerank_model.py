from __future__ import annotations
from typing import Any

import sys, os
import ipdb
import re
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

from transformers import OPTModel, GPT2Tokenizer, PreTrainedModel, PretrainedConfig
from premise_selection.training_types import PremiseBatch
from premise_selection.datamodule import tokenize_strings


class PremiseRerankerConfig(PretrainedConfig):
    model_type = "premise-reranker"
    model_name = "facebook/opt-125m"

    def __init__(self, **kwargs) -> None:
        super(PremiseRerankerConfig, self).__init__(**kwargs)


class PremiseReranker(PreTrainedModel):
    config_class = PremiseRerankerConfig

    def __init__(self, config: PremiseRerankerConfig) -> None:
        super(PremiseReranker, self).__init__(config)
        self.config = config
        self.decoder = OPTModel.from_pretrained(config.model_name)
        self.d_model = self.__get_d_model()
        self.final_projection = nn.Linear(self.d_model, 1, device=self.device)

    def __get_d_model(self) -> int:
        return int(
            self.decoder(
                self.decoder.dummy_inputs["input_ids"]
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
        hidden_states = self.decoder(
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
