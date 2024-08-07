from __future__ import annotations
from typing import Any, Optional
import json
from pathlib import Path

import argparse
from dataclasses import dataclass

from data_management.sentence_db import SentenceDB
from data_management.splits import DataSplit, get_all_files, FileInfo
from data_management.dataset_file import DatasetFile, StepID

from util.util import get_basic_logger

_logger = get_basic_logger(__name__)


@dataclass
class ProofDBPage:
    step_to_proof_map: dict[StepID, list[StepID]]

    def get(self, step_id: StepID) -> Optional[list[StepID]]:
        return self.step_to_proof_map.get(step_id)

    def to_json(self) -> Any:
        return {
            "step_to_proof_map": {
                key.to_string(): [val.to_string() for val in value]
                for key, value in self.step_to_proof_map.items()
            }
        }

    @classmethod
    def load(cls, path: Path) -> ProofDBPage:
        with open(path, "r") as f:
            return cls.from_json(json.load(f))

    @classmethod
    def from_json(cls, json_data: Any) -> ProofDBPage:
        return cls(
            {
                StepID.from_string(key): [StepID.from_string(val) for val in value]
                for key, value in json_data["step_to_proof_map"].items()
            }
        )


@dataclass
class RetrievedProofDB:
    proof_db_loc: Path
    CONF_NAME = "proof_retriever_conf.yaml"

    def get_steps(
        self, step_idx: int, proof_idx: int, dset_file: DatasetFile
    ) -> Optional[list[StepID]]:
        step_id = StepID.from_step_idx(step_idx, proof_idx, dset_file)
        page_loc = self.proof_db_loc / dset_file.dp_name
        page = ProofDBPage.load(page_loc)
        return page.get(step_id)

    def add_page(self, page: ProofDBPage, dset_file: DatasetFile):
        with open(self.proof_db_loc / dset_file.dp_name, "w") as f:
            json.dump(page.to_json(), f, indent=2)

    @classmethod
    def load(cls, path: Path) -> RetrievedProofDB:
        assert path.exists()
        assert (path / cls.CONF_NAME).exists()
        return cls(path)
