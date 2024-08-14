from __future__ import annotations
import json
import functools
from pathlib import Path
from typing import Optional, Any
from dataclasses import dataclass
from data_management.dataset_file import DatasetFile, Sentence
from data_management.sentence_db import SentenceDB

from proof_retrieval.retrieved_proof_db import StepID

from util.util import get_basic_logger

_logger = get_basic_logger(__name__)


@dataclass
class PremiseDBPage:
    step_to_premise_map: dict[StepID, list[Sentence]]

    def get(self, step_id: StepID) -> Optional[list[Sentence]]:
        return self.step_to_premise_map.get(step_id, [])

    def to_json(self, sentence_db: SentenceDB) -> Any:
        return {
            "step_to_premise_map": {
                key.to_string(): [val.to_json(sentence_db, False) for val in value]
                for key, value in self.step_to_premise_map.items()
            }
        }

    @classmethod
    def load(cls, path: Path, sentence_db: SentenceDB) -> PremiseDBPage:
        with open(path, "r") as fin:
            return cls.from_json(json.load(fin), sentence_db)

    @classmethod
    def from_json(cls, json_data: Any, sentence_db: Any) -> PremiseDBPage:
        return cls(
            {
                StepID.from_string(key): [
                    Sentence.from_json(val, sentence_db) for val in value
                ]
                for key, value in json_data["step_to_premise_map"].items()
            }
        )


@functools.lru_cache(128)
def load_page(path: Path, sentence_db: SentenceDB) -> PremiseDBPage:
    with open(path, "r") as fin:
        return PremiseDBPage.from_json(json.load(fin), sentence_db)


@dataclass
class RetrievedPremiseDB:
    premise_db_loc: Path
    CONF_NAME = "premise_retriever_conf.yaml"

    def get_premises(
        self,
        step_idx: int,
        proof_idx: int,
        dset_file: DatasetFile,
        sentence_db: SentenceDB,
    ) -> Optional[list[Sentence]]:
        step_id = StepID.from_step_idx(step_idx, proof_idx, dset_file)
        page_loc = self.premise_db_loc / dset_file.dp_name
        if not page_loc.exists():
            _logger.warning(f"Premise page not found: {page_loc}")
            return None
        page = load_page(page_loc, sentence_db)
        return page.get(step_id)

    @classmethod
    def load(cls, path: Path) -> RetrievedPremiseDB:
        assert path.exists()
        assert (path / cls.CONF_NAME).exists()
        return cls(path)


if __name__ == "__main__":
    sentence_db = SentenceDB.load(Path("raw-data/coq-dataset/sentences.db"))
    step_idx = 0
    proof_idx = 36
    dp = DatasetFile.load(
        Path("raw-data/coq-dataset/data_points/0918nobita-Coq-basics.v"), sentence_db
    )
    prem_db = RetrievedPremiseDB.load(Path("data/select-proj-thm-prem-db"))
    print(prem_db.get_premises(step_idx, proof_idx, dp, sentence_db))
