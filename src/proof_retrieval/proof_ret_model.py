from pathlib import Path

from transformers import AutoModel, PreTrainedModel, AutoTokenizer, PreTrainedTokenizer


class ProofRetrieverModel:
    def __init__(
        self, model: PreTrainedModel, tokenizer: PreTrainedTokenizer, max_seq_len: int
    ):
        self.model = model
        self.tokenizer = tokenizer
        self.max_seq_len = max_seq_len

    @classmethod
    def load_model(cls, model_name: str | Path) -> PreTrainedModel:
        model = AutoModel.from_pretrained(model_name)
