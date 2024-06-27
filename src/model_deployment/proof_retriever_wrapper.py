from __future__ import annotations
from typing import Any

from transformers import PreTrainedModel


class ProofRetrieverWrapper:
    def __init__(self, model: PreTrainedModel):
        self.model = model

    @classmethod
    def from_conf(cls, conf: Any) -> ProofRetrieverWrapper:
        pass
