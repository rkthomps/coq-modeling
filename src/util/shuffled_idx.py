from __future__ import annotations
from typing import Any
import json
import random
import argparse
from pathlib import Path
from dataclasses import dataclass
from tqdm import tqdm

from data_management.sentence_db import SentenceDB
from data_management.splits import DataSplit, Split
from data_management.dataset_file import StepID

from util.util import get_basic_logger

_logger = get_basic_logger(__name__)


@dataclass
class ShuffledIndex:
    def __init__(
        self,
        train_shuffled_idx: list[StepID],
        val_shuffled_idx: list[StepID],
        test_shuffled_idx: list[StepID],
    ):
        self.train_shuffled_idx = train_shuffled_idx
        self.val_shuffled_idx = val_shuffled_idx
        self.test_shuffled_idx = test_shuffled_idx

        self.reversed_train_idx = {
            step_id: idx for idx, step_id in enumerate(train_shuffled_idx)
        }
        self.reversed_val_idx = {
            step_id: idx for idx, step_id in enumerate(val_shuffled_idx)
        }
        self.reversed_test_idx = {
            step_id: idx for idx, step_id in enumerate(test_shuffled_idx)
        }

    def reversed_contains(self, split: Split, step_id: StepID) -> bool:
        match split:
            case Split.TRAIN:
                return step_id in self.reversed_train_idx
            case Split.VAL:
                return step_id in self.reversed_val_idx
            case Split.TEST:
                return step_id in self.reversed_test_idx

    def get_reversed_idx(self, split: Split, step_id: StepID) -> int:
        match split:
            case Split.TRAIN:
                return self.reversed_train_idx[step_id]
            case Split.VAL:
                return self.reversed_val_idx[step_id]
            case Split.TEST:
                return self.reversed_test_idx[step_id]

    def split_length(self, split: Split) -> int:
        match split:
            case Split.TRAIN:
                return len(self.train_shuffled_idx)
            case Split.VAL:
                return len(self.val_shuffled_idx)
            case Split.TEST:
                return len(self.test_shuffled_idx)

    def get_idx(self, split: Split, idx: int) -> StepID:
        match split:
            case Split.TRAIN:
                return self.train_shuffled_idx[idx]
            case Split.VAL:
                return self.val_shuffled_idx[idx]
            case Split.TEST:
                return self.test_shuffled_idx[idx]

    @classmethod
    def __get_shuffled_idx(
        cls,
        data_split: DataSplit,
        split: Split,
        data_loc: Path,
        sentence_db: SentenceDB,
    ) -> list[StepID]:
        unshuffled_idx: list[StepID] = []
        for f_info in tqdm(data_split.get_file_list(split)):
            file_dp = f_info.get_dp(data_loc, sentence_db)
            for proof_idx, proof in enumerate(file_dp.proofs):
                for step_idx, _ in enumerate(proof.steps):
                    unshuffled_idx.append(StepID(f_info.dp_name, proof_idx, step_idx))
        random.shuffle(unshuffled_idx)
        shuffled_idx = unshuffled_idx
        return shuffled_idx

    def to_json(self) -> Any:
        return {
            "train_shuffled_idx": [
                step_id.to_string() for step_id in self.train_shuffled_idx
            ],
            "val_shuffled_idx": [
                step_id.to_string() for step_id in self.val_shuffled_idx
            ],
            "test_shuffled_idx": [
                step_id.to_string() for step_id in self.test_shuffled_idx
            ],
        }

    def save(self, path: Path):
        with path.open("w") as fout:
            json.dump(self.to_json(), fout, indent=2)

    @classmethod
    def load(cls, path: Path) -> ShuffledIndex:
        with path.open("r") as fin:
            return cls.from_json(json.load(fin))

    @classmethod
    def from_json(cls, json_data: Any) -> ShuffledIndex:
        return cls(
            [
                StepID.from_string(step_id)
                for step_id in json_data["train_shuffled_idx"]
            ],
            [StepID.from_string(step_id) for step_id in json_data["val_shuffled_idx"]],
            [StepID.from_string(step_id) for step_id in json_data["test_shuffled_idx"]],
        )

    @classmethod
    def create(
        cls, data_split: DataSplit, data_loc: Path, sentence_db: SentenceDB
    ) -> ShuffledIndex:
        _logger.info("Getting Train Idx")
        shuffled_train = cls.__get_shuffled_idx(
            data_split, Split.TRAIN, data_loc, sentence_db
        )
        _logger.info("Getting Val Idx")
        shuffled_val = cls.__get_shuffled_idx(
            data_split, Split.VAL, data_loc, sentence_db
        )
        _logger.info("Getting Test Idx")
        shuffled_test = cls.__get_shuffled_idx(
            data_split, Split.TEST, data_loc, sentence_db
        )
        return cls(shuffled_train, shuffled_val, shuffled_test)


if __name__ == "__main__":
    parser = argparse.ArgumentParser("Create step-wise index for training.")
    parser.add_argument("--data_split_loc", type=str, required=True)
    parser.add_argument("--data_loc", type=str, required=True)
    parser.add_argument("--sentence_db_loc", type=str, required=True)
    parser.add_argument("--save_loc", type=str, required=True)

    args = parser.parse_args()
    data_split_loc = Path(args.data_split_loc)
    data_loc = Path(args.data_loc)
    sentence_db_loc = Path(args.sentence_db_loc)
    save_loc = Path(args.save_loc)

    assert data_split_loc.exists()
    assert data_loc.exists()
    assert sentence_db_loc.exists()

    if save_loc.exists():
        raise FileExistsError(f"{save_loc} already exists.")

    data_split = DataSplit.load(data_split_loc)
    sentence_db = SentenceDB.load(sentence_db_loc)
    shuffled_idx = ShuffledIndex.create(data_split, data_loc, sentence_db)

    shuffled_idx.save(save_loc)
