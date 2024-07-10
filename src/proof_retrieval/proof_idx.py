"""
An index from a proof's content and file to a global identifier.  
"""

from __future__ import annotations

import json
import hashlib

from pathlib import Path
import functools

from data_management.splits import FileInfo
from data_management.sentence_db import SentenceDB
from data_management.splits import DataSplit, get_all_files
from data_management.dataset_file import DatasetFile, Proof


@functools.cache
def hash_proof_step_str(step_idx: int, proof_str_id: str, dp_name: str) -> int:
    id_str = f"{step_idx}<Hi>{dp_name}<there!>{proof_str_id}"
    h = int.from_bytes(hashlib.md5(id_str.encode()).digest())
    return h


class ProofStateIdx:
    def __init__(self, proof_idx: dict[int, int]):
        self.proof_idx = proof_idx

    def save(self, path: Path):
        with path.open("w") as fout:
            fout.write(json.dumps(self.proof_idx, indent=2))

    def contains(self, idx: int) -> bool:
        return idx in self.proof_idx

    def get_idx(self, idx: int) -> int:
        return self.proof_idx[idx]

    @classmethod
    def load(cls, path: Path) -> ProofStateIdx:
        with path.open("r") as fin:
            proof_idx = json.load(fin)
            return cls(proof_idx)

    @classmethod
    def hash_proof_step(cls, step_idx: int, proof: Proof, dp_name: str) -> int:
        proof_content = proof.proof_text_id()
        return hash_proof_step_str(step_idx, proof_content, dp_name)


class ProofScriptIdx:
    def __init__(self, proof_idx: dict[int, int]):
        self.proof_idx = proof_idx

    def contains(self, idx: int) -> bool:
        return idx in self.proof_idx

    def get_idx(self, idx: int) -> int:
        return self.proof_idx[idx]

    def save(self, path: Path):
        with path.open("w") as fout:
            fout.write(json.dumps(self.proof_idx, indent=2))

    @classmethod
    def load(cls, path: Path) -> ProofScriptIdx:
        with path.open("r") as fin:
            proof_idx = json.load(fin)
            return cls(proof_idx)

    @classmethod
    def hash_proof_step(cls, step_idx: int, proof: Proof, dp_name: str) -> int:
        proof_content = proof.proof_text_id()
        id_str = f"{dp_name}<there!>{proof_content}"
        h = int.from_bytes(hashlib.md5(id_str.encode()).digest())
        return h


ProofIdx = ProofStateIdx | ProofScriptIdx
