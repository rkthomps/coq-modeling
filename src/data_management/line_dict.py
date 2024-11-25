"""
Dictionary with the n lines preceding a proof.
"""

from __future__ import annotations
from typing import Any
import json
import ipdb
from tqdm import tqdm

import sys, os
import shutil
import json
import argparse
from pathlib import Path
import multiprocessing as mp
from multiprocessing import set_start_method

from data_management.create_file_data_point import DATASET_PREFIX
from data_management.splits import FileInfo, REPOS_NAME, DATA_POINTS_NAME
from data_management.dataset_file import DatasetFile, Proof, SentenceDB
from data_management.splits import DataSplit, Split
from model_deployment.fast_client import FastLspClient, ClientWrapper

from util.util import get_fresh_path
from util.constants import TMP_LOC, RANGO_LOGGER
import logging

_logger = logging.getLogger(RANGO_LOGGER)


class LineDict:
    def __init__(self, line_num_dict: dict[str, list[int]]):
        self.line_num_dict = line_num_dict

    def to_json(self) -> Any:
        return {"line_num_dict": self.line_num_dict}

    def has_file(self, file_name: str) -> bool:
        return file_name in self.line_num_dict

    def get(self, file_name: str, proof_idx: int) -> int:
        return self.line_num_dict[file_name][proof_idx]

    @classmethod
    def from_json(cls, json_data: Any) -> LineDict:
        return LineDict(json_data["line_num_dict"])

    def save(self, path: Path):
        with path.open("w") as f:
            f.write(json.dumps(self.to_json()))

    @classmethod
    def load(cls, path: Path) -> LineDict:
        with path.open("r") as f:
            return cls.from_json(json.load(f))


def read_file(p: Path) -> str:
    with p.open("r") as f:
        return f.read()


LSP_LOC = TMP_LOC / "lines"


def normalize(s: str) -> str:
    return " ".join(s.split())


def find_dp_lines(proofs: list[Proof]) -> list[int]:
    return [p.theorem.term.line for p in proofs]


def find_lines(data_loc: Path, sentence_db_loc: Path) -> LineDict:
    sentence_db = SentenceDB.load(sentence_db_loc)
    line_dict: dict[str, list[int]] = {}
    for dp_loc in tqdm(list((data_loc / DATA_POINTS_NAME).iterdir())):
        dp = DatasetFile.load(dp_loc, sentence_db)
        dp_lines = find_dp_lines(dp.proofs)
        data_loc_root = Path(DATASET_PREFIX).parent
        assert Path(dp.file_context.file).is_relative_to(
            data_loc_root
        ), f"{dp.file_context.file} not relative to {data_loc_root}"
        line_dict[str(Path(dp.file_context.file).relative_to(data_loc_root))] = dp_lines
    return LineDict(line_dict)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("data_loc", help="Path to raw dataset.")
    parser.add_argument("sentence_db_loc", help="Path to sentence db.")
    parser.add_argument("out_loc", help="Path to output directory.")

    args = parser.parse_args(sys.argv[1:])
    data_loc = Path(args.data_loc)
    sentence_db_loc = Path(args.sentence_db_loc)
    out_loc = Path(args.out_loc)

    if out_loc.exists():
        yesno = input(f"{out_loc} exists. Overwrite? (y/n) ")
        if yesno != "y":
            raise FileExistsError(f"{out_loc} exists.")
        os.remove(out_loc)

    line_dict = find_lines(data_loc, sentence_db_loc)

    _logger.info("Saving")
    line_dict.save(out_loc)
