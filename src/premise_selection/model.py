from __future__ import annotations
from typing import Any

from enum import Enum

from transformers import (
    OPTModel,
)
import torch
import torch.nn.functional as F
from yaml import load, Loader

from transformers import PreTrainedModel, PretrainedConfig
from premise_selection.training_types import PremiseBatch
from premise_selection.select_data import tokenize_strings


class PremiseRetrieverConfig(PretrainedConfig):
    model_type = "premise-retriever"
    model_name = "facebook/opt-125m"

    def __init__(self, **kwargs) -> None:
        super(PremiseRetrieverConfig, self).__init__(**kwargs)


class EncodeType(Enum):
    PREMISE = 1
    CONTEXT = 2


class PremiseRetriever(PreTrainedModel):
    config_class = PremiseRetrieverConfig

    def __init__(self, config: PremiseRetrieverConfig) -> None:
        super(PremiseRetriever, self).__init__(config)
        self.config = config
        self.decoder = OPTModel.from_pretrained(config.model_name)
        self.d_model = self.__get_d_model()
        self.premise_projection = torch.nn.Linear(
            self.d_model, self.d_model, device=self.device
        )
        self.context_projection = torch.nn.Linear(
            self.d_model, self.d_model, device=self.device
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

    def encode_premise(
        self, input_ids: torch.Tensor, mask: torch.Tensor
    ) -> torch.Tensor:
        avg_embedding = self._get_avg_embedding(input_ids, mask)
        proj_embedding = self.premise_projection(avg_embedding)
        return F.normalize(proj_embedding, dim=1)

    def encode_context(
        self, input_ids: torch.Tensor, mask: torch.Tensor
    ) -> torch.Tensor:
        avg_embedding = self._get_avg_embedding(input_ids, mask)
        proj_embedding = self.context_projection(avg_embedding)
        return F.normalize(proj_embedding, dim=1)

    def forward(
        self,
        context_ids: torch.Tensor,
        context_mask: torch.Tensor,
        premise_ids: torch.Tensor,
        premise_mask: torch.Tensor,
        label: torch.Tensor,
    ) -> dict[str, torch.Tensor]:
        context_embs = self.encode_context(context_ids, context_mask)
        premise_embs = self.encode_premise(premise_ids, premise_mask)
        similarity = torch.mm(context_embs, premise_embs.t())
        epsilon = 1e-4
        assert (-1 - epsilon) <= similarity.min() <= similarity.max() <= (1 + epsilon)
        return {"similarities": similarity}
