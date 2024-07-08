from __future__ import annotations
from typing import Optional

from dataclasses import dataclass
from pathlib import Path
from proof_retrieval.proof_idx import ProofIdx
from util.vector_db_utils import get_embs, get

from data_management.dataset_file import Proof, DatasetFile
from data_management.splits import DataSplit

import torch
from transformers import PreTrainedModel, PreTrainedTokenizer


@dataclass
class ProofDBQuery:
    step_idx: int
    proof: Proof
    dp_file: DatasetFile


def load_encoder(name: str | Path) -> 

class ProofVectorDB:
    def __init__(self, db_loc: Path, page_size: int, source: str, proof_idx: ProofIdx):
        self.db_loc = db_loc
        self.page_size = page_size
        self.source = source
        self.proof_idx = proof_idx
        self.device = "cpu"

    def get_embs(self, queries: list[ProofDBQuery]) -> Optional[torch.Tensor]:
        idxs = [
            self.proof_idx.hash_proof_step(q.step_idx, q.proof, q.dp_file)
            for q in queries
        ]
        return get_embs(idxs, self.page_size, self.db_loc, self.device)

    @classmethod
    def create_proof_db(
        cls,
        db_loc: Path,
        page_size: int,
        batch_size: int,
        source: str,
        data_splits: list[DataSplit],
    ) -> ProofVectorDB:

        pass
