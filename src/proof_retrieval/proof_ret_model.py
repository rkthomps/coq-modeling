from __future__ import annotations
from pathlib import Path

import torch
import torch.nn.functional as F
from transformers import AutoModel, PreTrainedModel, AutoTokenizer, PreTrainedTokenizer


class RawProofRetrieverModel:
    def __init__(
        self, model: PreTrainedModel, tokenizer: PreTrainedTokenizer, max_seq_len: int
    ):
        self.model = model
        self.tokenizer = tokenizer
        self.max_seq_len = max_seq_len

    def encode(self, ss: list[str]) -> torch.Tensor:
        inputs = self.tokenizer(
            ss,
            padding=True,
            truncation=True,
            max_length=self.max_seq_len,
            return_tensors="pt",
        ).to(self.model.device)
        last_state = self.model(**inputs).last_hidden_state  # B x S x D
        avg_last_state = torch.mean(last_state, dim=1)  # B x D
        return F.normalize(avg_last_state, dim=1)

    def to(self, device: int):
        self.model.to(f"cuda:{device}")

    @classmethod
    def load_model(
        cls, model_name: str | Path, max_seq_len: int
    ) -> RawProofRetrieverModel:
        model = AutoModel.from_pretrained(model_name)
        tokenizer = AutoTokenizer.from_pretrained(model_name)
        return cls(model, tokenizer, max_seq_len)


ProofRetrievalModel = RawProofRetrieverModel
