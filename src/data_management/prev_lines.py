"""
Dictionary with the n lines preceding a proof.
"""

from __future__ import annotations
from typing import Any
import ipdb

import sys, os
import json
from pathlib import Path

from data_management.splits import FileInfo, REPOS_NAME
from data_management.dataset_file import DatasetFile, Proof, SentenceDB
from data_management.splits import DataSplit, Split
from model_deployment.fast_client import FastLspClient, ClientWrapper

from util.util import _logger, get_fresh_path
from util.constants import TMP_LOC


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


def read_file(p: Path) -> str:
    with p.open("r") as f:
        return f.read()


LSP_LOC = TMP_LOC / "lines"


def normalize(s: str) -> str:
    return " ".join(s.split())


def check_valid(client_wrapper: ClientWrapper) -> bool:
    for diagnostic in client_wrapper.client.lsp_endpoint.diagnostics[
        client_wrapper.file_uri
    ]:
        if diagnostic.severity == 1:
            return False
    return True


def hacky_find_lines(proofs: list[Proof], contents: str) -> list[int]:
    content_lines = contents.split("\n")
    cur_line = 0
    lines: list[int] = []
    for p in proofs:

        # Move end forward
        end = cur_line
        target_str = normalize(" ".join(content_lines[cur_line:end]))
        assert normalize(p.theorem.term.text) not in target_str
        while normalize(p.theorem.term.text) not in target_str:
            end += 1
            target_str = normalize(" ".join(content_lines[cur_line:end]))

        # Move cur foward
        target_str = normalize(" ".join(content_lines[cur_line:end]))
        assert normalize(p.theorem.term.text) in target_str
        while normalize(p.theorem.term.text) in target_str:
            cur_line += 1
            target_str = normalize(" ".join(content_lines[cur_line:end]))
        lines.append(cur_line - 1)
    assert len(lines) == len(proofs)
    return lines


def find_file_lines(
    file_info: FileInfo, data_loc: Path, sentence_db_loc: Path
) -> list[int]:
    sentence_db = SentenceDB.load(sentence_db_loc)
    file_proofs = file_info.get_proofs(data_loc, sentence_db)
    return hacky_find_lines(file_proofs, read_file(data_loc / file_info.file))
    # client = FastLspClient(file_info.workspace, timeout=120)
    # fresh_path = get_fresh_path(LSP_LOC, "lines_file.v")
    # try:
    #     file_uri = f"file://{fresh_path.resolve()}"
    #     client_wrapper = ClientWrapper(client, file_uri)
    #     file_contents = read_file(data_loc / file_info.file)
    #     os.makedirs(LSP_LOC, exist_ok=True)
    #     steps = client_wrapper.write_and_get_steps(file_contents)
    #     print("Valid: ", check_valid(client_wrapper))
    #     cur_step = 0
    #     lines: list[int] = []
    #     for i, proof in enumerate(file_proofs):
    #         while cur_step < len(steps) and normalize(
    #             proof.theorem.term.text
    #         ) not in normalize(steps[cur_step].text):
    #             cur_step += 1
    #         if len(steps) <= cur_step:
    #             print(f"{[s.text for s in steps]}")
    #             raise ValueError(
    #                 f"Proof {proof.theorem.term.text} (idx {i}) not found in {file_info.file}."
    #             )
    #         lines.append(steps[cur_step].ast.range.start.line)
    #     return lines
    # finally:
    #     client.kill()
    #     if os.path.exists(fresh_path):
    #         os.remove(fresh_path)


if __name__ == "__main__":
    data_loc = Path("raw-data/coq-dataset")
    sentence_db_loc = Path("raw-data/coq-dataset/sentences.db")
    data_split = DataSplit.load(Path("splits/final-split.json"))

    for file_info in data_split.get_file_list(Split.TEST):
        _logger.info(f"Processing {file_info.file}")
        find_file_lines(file_info, data_loc, sentence_db_loc)
