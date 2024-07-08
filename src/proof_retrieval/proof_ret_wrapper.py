from __future__ import annotations
from typing import Optional
from pathlib import Path
from proof_retrieval.proof_ret_model import ProofRetrievalModel
from proof_retrieval.proof_idx import ProofIdx
from proof_retrieval.proof_vector_db import ProofVectorDB
from transformers import PreTrainedModel, AutoModel, AutoTokenizer, PreTrainedTokenizer


class ProofRetWrapper:
    ALIAS = "pretrained"

    def __init__(self, model: ProofRetrievalModel, proof_vector_db: ProofVectorDB):
        self.model = model
        self.proof_vector_db = proof_vector_db

    def get_scores(self, key_proof_str: str, avail_indices: list[int]) -> list[float]:
        query_encoding = self.model.encode([key_proof_str])
        document_encoding = self.proof_vector_db.get_embs(avail_indices).to(
            query_encoding.device
        )
        similarities = (query_encoding @ document_encoding.T).squeeze().tolist()
        return similarities

    @classmethod
    def from_model_name(
        cls, name: str | Path, max_seq_len: int, vector_db_loc: Path
    ) -> ProofRetWrapper:
        model = ProofRetrievalModel.load_model(name, max_seq_len)
        proof_vector_db = ProofVectorDB.load(vector_db_loc)
        return cls(model, proof_vector_db)
