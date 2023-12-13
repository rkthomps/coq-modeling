from __future__ import annotations
from typing import Any, Generator

import os
import re
import shutil
import datetime
import random
from data_management.splits import FileInfo, DataSplit, Split, str2split
from util.util import get_basic_logger

from coqpyt.coq.proof_file import ProofFile
from coqpyt.coq.base_file import CoqFile
from coqpyt.coq.structs import Step

_logger = get_basic_logger(__name__)


class ProofInfo:
    def __init__(
        self,
        file_loc: str,
        proof_file: ProofFile,
        idx: int,
    ) -> None:
        self.file_loc = file_loc
        self.proof_file = proof_file
        self.idx = idx

    def statement(self) -> str:
        return self.proof_file.steps[self.idx].text

    def ground_truth_steps(self) -> list[str]:
        return [s.text for s in get_proof_steps(self.proof_file, self.idx)]


def __eval_to(proof_file: ProofFile, i: int) -> None:
    while proof_file.steps_taken < i:
        proof_file.exec(1)
    while i < proof_file.steps_taken:
        proof_file.exec(-1)


def get_proof_indices(proof_file: ProofFile) -> list[int]:
    __eval_to(proof_file, 0)
    cur_in_proof = False
    indices: list[int] = []
    while proof_file.steps_taken < len(proof_file.steps):
        proof_file.exec(1)
        if not cur_in_proof and proof_file.in_proof:
            indices.append(proof_file.steps_taken - 1)
            cur_in_proof = True
        if not proof_file.in_proof:
            cur_in_proof = False
    return indices


def get_proof_steps(proof_file: ProofFile, i: int) -> list[Step]:
    __eval_to(proof_file, i + 1)
    assert proof_file.in_proof
    steps: list[Step] = []
    while proof_file.in_proof and proof_file.steps_taken < len(proof_file.steps):
        steps.append(proof_file.steps[proof_file.steps_taken])
        proof_file.exec(1)
    return steps


def thm_lemma_qed_filter(proof_file: ProofFile, i: int) -> bool:
    is_thm = "Theorem" in proof_file.steps[i].text
    is_lemma = "Lemma" in proof_file.steps[i].text
    proof_steps = get_proof_steps(proof_file, i)
    ends_with_qed = "Qed" in proof_steps[-1].text
    return (is_thm or is_lemma) and ends_with_qed


class DataSplitEvalSet:
    def __init__(
        self,
        data_split: DataSplit,
        split: Split,
        data_loc: str,
        eval_tmp_loc: str,
        seed: int,
    ) -> None:
        self.data_split = data_split
        self.split = split
        self.data_loc = data_loc
        self.eval_tmp_loc = eval_tmp_loc
        self.seed = seed

    def get_file_gen(self) -> Generator[FileInfo, None, None]:
        random.seed(self.seed)
        projects = self.data_split.get_project_list(self.split)
        files: list[FileInfo] = []
        for p in projects:
            files.extend(p.files)
        random.shuffle(files)
        for file in files:
            yield file

    def rough_proof_count(self, file_info: FileInfo) -> int:
        file_loc = os.path.join(self.data_loc, file_info.file)
        with open(file_loc, "r") as fin:
            return len(re.findall(r"Qed.", fin.read()))

    def get_proof_gen(self, file_info: FileInfo) -> Generator[ProofInfo, None, None]:
        _logger.debug(f"Finding proofs to evaluate {file_info.file}")
        file_loc = os.path.join(self.data_loc, file_info.file)
        eval_file_loc = os.path.join(self.eval_tmp_loc, file_info.file)
        _logger.debug(f"Eval loc: {eval_file_loc}")
        eval_file_dir = os.path.dirname(eval_file_loc)
        if not os.path.exists(file_loc):
            _logger.warning(f"File {file_loc} doesn't exist.")
            raise FileNotFoundError(file_loc)
        os.makedirs(eval_file_dir, exist_ok=True)
        shutil.copy(file_loc, eval_file_loc)
        workspace_loc = os.path.join(self.data_loc, file_info.workspace)
        _logger.debug(f"Workspace: {workspace_loc}")
        with CoqFile(eval_file_loc, workspace=workspace_loc) as coq_file:
            if not coq_file.is_valid:
                _logger.info(f"{file_loc} not valid. Moving on.")
                return
        with ProofFile(eval_file_loc, workspace=workspace_loc) as proof_file:
            proof_begin_indices = get_proof_indices(proof_file)
            filtered_indices = [
                idx
                for idx in proof_begin_indices
                if thm_lemma_qed_filter(proof_file, idx)
            ]
            for index in filtered_indices:
                yield ProofInfo(eval_file_loc, proof_file, index)

    @classmethod
    def from_conf(cls, conf: Any) -> DataSplitEvalSet:
        data_split = DataSplit.load(conf["data_split_loc"])
        split = str2split(conf["split"])
        data_loc = conf["data_loc"]
        eval_tmp_dir = conf["eval_tmp_dir"]
        seed = conf["seed"]

        cur_time = datetime.datetime.now()
        time_name = cur_time.strftime("%Y-%m-%d:%H:%M:%S")
        eval_tmp_loc = os.path.join(eval_tmp_dir, time_name)
        return cls(data_split, split, data_loc, eval_tmp_loc, seed)
