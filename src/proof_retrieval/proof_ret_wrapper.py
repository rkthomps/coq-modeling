from __future__ import annotations
from transformers import PreTrainedModel, AutoModel, AutoTokenizer, PreTrainedTokenizer


class ProofRetWrapper:
    ALIAS = "pretrained"

    def __init__(
        self, model: PreTrainedModel, tokenizer: PreTrainedTokenizer, max_seq_len: int
    ):
        self.model = model
        self.tokenizer = tokenizer
        self.max_seq_len = max_seq_len

    def get_scores(self, key_proof: str, proofs: list[str]) -> list[float]:
        key_ids = self.tokenizer()
        raise NotImplementedError

    @classmethod
    def from_model_name(cls, name: str) -> ProofRetWrapper:
        model = AutoModel.from_pretrained(name)
        tokenizer = AutoTokenizer.from_pretrained(name)
        return cls(model, tokenizer)
