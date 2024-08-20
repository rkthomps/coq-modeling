"""
Dictionary with the n lines preceding a proof.
"""

from __future__ import annotations
from typing import Any
import json
import ipdb

import sys, os
import shutil
import json
import argparse
from pathlib import Path
import multiprocessing as mp
from multiprocessing import set_start_method

from data_management.splits import FileInfo, REPOS_NAME, DATA_POINTS_NAME
from data_management.dataset_file import DatasetFile, Proof, SentenceDB
from data_management.splits import DataSplit, Split
from model_deployment.fast_client import FastLspClient, ClientWrapper

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


def str_find_lines(proofs: list[Proof], contents: str) -> list[int]:
    content_lines = contents.split("\n")
    cur_line = 0
    lines: list[int] = []
    for p in proofs:

        # Move end forward
        end = cur_line
        target_str = normalize(" ".join(content_lines[cur_line:end]))
        assert normalize(p.theorem.term.text) not in target_str
        while (
            end <= len(content_lines)
            and normalize(p.theorem.term.text) not in target_str
        ):
            end += 1
            target_str = normalize(" ".join(content_lines[cur_line:end]))

        # Move cur foward
        target_str = normalize(" ".join(content_lines[cur_line:end]))
        assert normalize(p.theorem.term.text) in target_str
        while (
            cur_line < len(content_lines)
            and normalize(p.theorem.term.text) in target_str
        ):
            cur_line += 1
            target_str = normalize(" ".join(content_lines[cur_line:end]))
        lines.append(cur_line - 1)
    assert len(lines) == len(proofs)
    return lines


def find_file_lines(
    file_info: FileInfo, data_loc: Path, sentence_db_loc: Path, tmp_out_loc: Path
) -> None:
    try:
        sentence_db = SentenceDB.load(sentence_db_loc)
        file_proofs = file_info.get_proofs(data_loc, sentence_db)
        line_indices = str_find_lines(file_proofs, read_file(data_loc / file_info.file))
        os.makedirs(tmp_out_loc, exist_ok=True)
        with open(tmp_out_loc / file_info.dp_name, "w") as fout:
            fout.write(json.dumps(line_indices))
        sentence_db.close()
    except:
        _logger.error(f"Error processing {file_info.file}")


def get_all_file_infos(data_splits: list[DataSplit]) -> list[FileInfo]:
    file_infos: set[FileInfo] = set()
    for ds in data_splits:
        for s in Split:
            file_infos |= set(ds.get_file_list(s))
    return list(file_infos)


def consolidate(tmp_out_loc: Path, file_infos: list[FileInfo]) -> LineDict:
    line_dict: dict[str, list[int]] = {}
    for f_info in file_infos:
        nums_loc = tmp_out_loc / f_info.dp_name
        if not nums_loc.exists():
            _logger.error(f"Could not find file {nums_loc}.")
            continue
        with nums_loc.open("r") as fin:
            line_idxs = json.load(fin)
            line_dict[f_info.file] = line_idxs
    return LineDict(line_dict)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("data_loc", help="Path to raw dataset.")
    parser.add_argument("sentence_db_loc", help="Path to sentence db.")
    parser.add_argument("out_loc", help="Path to output directory.")
    parser.add_argument("n_procs", type=int, help="Number of processes.")
    parser.add_argument("split_locs", nargs="+", help="Paths to split locations.")

    args = parser.parse_args(sys.argv[1:])
    data_loc = Path(args.data_loc)
    sentence_db_loc = Path(args.sentence_db_loc)
    out_loc = Path(args.out_loc)
    n_procs = args.n_procs
    data_splits = [DataSplit.load(Path(l)) for l in args.split_locs]

    if out_loc.exists():
        yesno = input(f"{out_loc} exists. Overwrite? (y/n) ")
        if yesno != "y":
            raise FileExistsError(f"{out_loc} exists.")
        os.remove(out_loc)

    tmp_out_loc = get_fresh_path(TMP_LOC, "lines")
    file_infos = get_all_file_infos(data_splits)
    args = [(f, data_loc, sentence_db_loc, tmp_out_loc) for f in file_infos]

    set_start_method("spawn")

    with mp.Pool(n_procs) as pool:
        pool.starmap(find_file_lines, args)

    _logger.info("Consolidating")
    line_dict = consolidate(tmp_out_loc, file_infos)
    _logger.info("Saving")
    line_dict.save(out_loc)

    _logger.info("Cleaning up")
    if tmp_out_loc.exists():
        shutil.rmtree(tmp_out_loc)
