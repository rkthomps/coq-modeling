"""
An index from a proof's content and file to a global identifier.  
"""

from __future__ import annotations

import json

from pathlib import Path

from data_management.sentence_db import SentenceDB
from data_management.splits import DataSplit, get_all_files
from data_management.dataset_file import DatasetFile, Proof


class ProofStateIdx:
    def __init__(self, proof_idx: dict[int, int]):
        self.proof_idx = proof_idx

    def save(self, path: Path):
        with path.open("w") as fout:
            fout.write(json.dumps(self.proof_idx, indent=2))

    @classmethod
    def load(cls, path: Path) -> ProofStateIdx:
        with path.open("r") as fin:
            proof_idx = json.load(fin)
            return cls(proof_idx)

    @classmethod
    def hash_proof_step(cls, step_idx: int, proof: Proof, dp_file: DatasetFile) -> int:
        proof_content = proof.proof_text_to_string()
        proof_file = dp_file.file_context.file
        return hash((proof_file, proof_content))


class ProofScriptIdx:
    def __init__(self, proof_idx: dict[int, int]):
        self.proof_idx = proof_idx

    def save(self, path: Path):
        with path.open("w") as fout:
            fout.write(json.dumps(self.proof_idx, indent=2))

    @classmethod
    def load(cls, path: Path) -> ProofScriptIdx:
        with path.open("r") as fin:
            proof_idx = json.load(fin)
            return cls(proof_idx)

    @classmethod
    def hash_proof_step(cls, step_idx: int, proof: Proof, dp_file: DatasetFile) -> int:
        proof_content = proof.proof_text_to_string()
        proof_file = dp_file.file_context.file
        return hash((step_idx, proof_file, proof_content))


ProofIdx = ProofStateIdx | ProofScriptIdx


