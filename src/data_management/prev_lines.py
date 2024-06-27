"""
Dictionary with the n lines preceding a proof.
"""

from __future__ import annotations
from typing import Any

import json
from pathlib import Path

from data_management.splits import FileInfo, REPOS_NAME
from data_management.dataset_file import DatasetFile, Proof, SentenceDB
from data_management.splits import DataSplit, Split

from util.util import _logger


class PrevLineDict:
    def __init__(self, line_num_dict: dict[tuple[FileInfo, int], int]):
        self.line_num_dict = line_num_dict

    def to_json(self) -> list[dict[str, Any]]:
        ret_obj: list[dict[str, Any]] = []
        for k, v in self.line_num_dict.items():
            file_info, proof_idx = k
            line_dict = {
                "key": {"file_info": file_info.to_json(), "proof_idx": proof_idx},
                "value": v,
            }
            ret_obj.append(line_dict)
        return ret_obj

    @classmethod
    def from_json(cls, json_data: Any) -> PrevLineDict:
        n_line_dict = {}
        for line_dict in json_data:
            key = line_dict["key"]
            file_info = FileInfo.from_json(key["file_info"])
            proof_idx = key["proof_idx"]
            n_line_dict[(file_info, proof_idx)] = line_dict["value"]
        return PrevLineDict(n_line_dict)

    def save(self, path: Path):
        with path.open("w") as f:
            f.write(json.dumps(self.to_json()))

    @classmethod
    def load(cls, path: Path) -> PrevLineDict:
        with path.open("r") as f:
            return cls.from_json(json.load(f))


def find_file_lines(
    file_info: FileInfo, data_loc: Path, sentence_db: SentenceDB
) -> list[int]:
    file_proofs = file_info.get_proofs(data_loc, sentence_db)
    line_nums: list[int] = []
    target_file = data_loc / file_info.file
    assert target_file.exists()
    with target_file.open("r") as fin:
        target_content = fin.read()

    for i, proof in enumerate(file_proofs):
        proof_text = proof.proof_text_to_string(include_theorem=False)
        if proof_text not in target_content:
            print(f"<<<<<PROOF TEXT for {proof.get_theorem_name()}>>>>>")
            print(proof_text)
            print("<<<<<FILE TEXT>>>>>>>")
            print(target_content)
            exit()
    return []


if __name__ == "__main__":
    data_loc = Path("raw-data/coq-dataset")
    sentence_db_loc = Path("raw-data/coq-dataset/sentences.db")
    data_split = DataSplit.load(Path("splits/final-split.json"))

    for file_info in data_split.get_file_list(Split.TEST):
        _logger.info(f"Processing {file_info.file}")
        find_file_lines(file_info, data_loc, SentenceDB.load(sentence_db_loc))
