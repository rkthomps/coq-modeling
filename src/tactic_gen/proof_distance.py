from __future__ import annotations
from typeguard import typechecked
from typing import Optional, Any
import traceback
import datetime
import logging
import heapq
import argparse
import os
import sys
import json
from tqdm import tqdm

from util.util import get_basic_logger

_logger = get_basic_logger(__name__)

from data_management.splits import (
    DataSplit,
    FileInfo,
    Split,
    split2str,
    str2split,
)
from data_management.dataset_file import Proof

from util.util import get_simple_steps
from tactic_gen.tactic_pair_encoding import TacticPairEncoding
from tactic_gen.step_parser import CoqParseError


def levenshtein_dist_fast(strs1: list[str], strs2: list[str]) -> int:
    scores: list[list[int]] = []
    for i in range(len(strs1) + 1):
        cur_row: list[int] = []
        for j in range(len(strs2) + 1):
            if i == 0:
                cur_row.append(j)
            elif j == 0:
                cur_row.append(i)
            elif strs1[i - 1] == strs2[j - 1]:
                cur_row.append(scores[i - 1][j - 1])
            else:
                cur_row.append(
                    1 + min(scores[i - 1][j - 1], cur_row[j - 1], scores[i - 1][j])
                )
        scores.append(cur_row)
    return scores[len(strs1)][len(strs2)]


ProblemKey = tuple[tuple[str, ...], tuple[str, ...]]


def __get_problem_key(k1: list[str], k2: list[str]) -> ProblemKey:
    return tuple(k1), tuple(k2)


def levenshtein_dist(
    norm_steps1: list[str],
    norm_steps2: list[str],
    subproblems: Optional[dict[ProblemKey, int]] = None,
) -> int:
    if subproblems is None:
        subproblems = {}
    result: Optional[int] = None
    problem_key = __get_problem_key(norm_steps1, norm_steps2)
    if problem_key in subproblems:
        return subproblems[problem_key]

    if len(norm_steps1) == 0:
        result = len(norm_steps2)
    elif len(norm_steps2) == 0:
        result = len(norm_steps1)

    elif norm_steps1[0] == norm_steps2[0]:
        result = levenshtein_dist(norm_steps1[1:], norm_steps2[1:], subproblems)
    else:
        result = 1 + min(
            levenshtein_dist(norm_steps1, norm_steps2[1:], subproblems),
            levenshtein_dist(norm_steps1[1:], norm_steps2, subproblems),
            levenshtein_dist(norm_steps1[1:], norm_steps2[1:], subproblems),
        )

    subproblems[problem_key] = result
    return result


def norm_levenshtein_dist(proof1: Proof, proof2: Proof) -> float:
    try:
        proof1_norm_steps = [
            TacticPairEncoding.normalize_step(s.step.text) for s in proof1.steps
        ]
        proof2_norm_steps = [
            TacticPairEncoding.normalize_step(s.step.text) for s in proof2.steps
        ]
        max_distance = max(len(proof1_norm_steps), len(proof2_norm_steps))
        raw_lev_dist = levenshtein_dist_fast(proof1_norm_steps, proof2_norm_steps)
        return raw_lev_dist / max_distance
    except:
        return 1


@typechecked
class StrippedProof:
    def __init__(
        self,
        creation_time: datetime.datetime,
        file: FileInfo,
        line: int,
        thm: str,
        steps: list[str],
        norm_steps: Optional[list[str]],
        split: Split,
    ) -> None:
        self.creation_time = creation_time
        self.file = file
        self.line = line
        self.thm = thm
        self.steps = steps
        self.norm_steps = norm_steps
        self.split = split

    def to_string(self) -> str:
        return self.thm + "".join(self.steps)

    def to_json(self) -> Any:
        return {
            "creation_time": self.creation_time.isoformat(),
            "file": self.file.to_json(),
            "line": self.line,
            "thm": self.thm,
            "steps": self.steps,
            "norm_steps": self.norm_steps,
            "split": split2str(self.split),
        }

    @classmethod
    def from_proof(
        cls,
        proof: Proof,
        file_info: FileInfo,
        creation_time: datetime.datetime,
        split: Split,
    ) -> StrippedProof:
        line = proof.theorem.term.line
        thm = proof.theorem.term.text
        steps = [s.step.text for s in proof.steps]
        try:
            norm_steps = [TacticPairEncoding.normalize_step(s) for s in steps]
        except CoqParseError:
            norm_steps = None
        return StrippedProof(
            creation_time, file_info, line, thm, steps, norm_steps, split
        )

    @classmethod
    def from_steps(cls, steps: list[str]) -> StrippedProof:
        thm = "Lemma psuedo: False."
        file = FileInfo("notafile", "notafile", "notaworkspace", "notarepo")
        line = -1
        try:
            norm_steps = [TacticPairEncoding.normalize_step(s) for s in steps]
        except CoqParseError:
            norm_steps = None
        split = Split.TRAIN
        return StrippedProof(
            datetime.datetime.now(), file, line, thm, steps, norm_steps, split
        )

    @classmethod
    def from_text(cls, text: str) -> StrippedProof:
        steps = get_simple_steps(text)
        return cls.from_steps(steps)

    @classmethod
    def from_json(cls, json_data: Any) -> StrippedProof:
        creation_time = datetime.datetime.fromisoformat(json_data["creation_time"])
        file = FileInfo.from_json(json_data["file"])
        line = json_data["line"]
        thm = json_data["thm"]
        steps = json_data["steps"]
        norm_steps = json_data["norm_steps"]
        split = str2split(json_data["split"])
        return cls(creation_time, file, line, thm, steps, norm_steps, split)


class SimilarProofCandidate:
    def __init__(self, score: float, proof: StrippedProof) -> None:
        self.score = score
        self.proof = proof

    # since lower is better, want to store the highest at the top of heap
    def __lt__(self, other: SimilarProofCandidate) -> bool:
        return other.score < self.score

    def __le__(self, other: SimilarProofCandidate) -> bool:
        return other.score <= self.score


@typechecked
class SortedProofs:
    def __init__(self, ordered_proofs: list[StrippedProof]) -> None:
        self.ordered_proofs = ordered_proofs
        assert len(ordered_proofs) > 0
        assert self.is_ordered()

    def is_ordered(self) -> bool:
        for i in range(len(self.ordered_proofs) - 1):
            cur_key = self.__ordering_key(self.ordered_proofs[i])
            next_key = self.__ordering_key(self.ordered_proofs[i + 1])
            if cur_key > next_key:
                return False
        return True

    def __find_first_match(self, proposed_idx: int, target_key: int) -> Optional[int]:
        assert 0 <= proposed_idx < len(self.ordered_proofs)
        first_match: Optional[int] = None
        cur_idx = proposed_idx
        while (
            0 <= cur_idx
            and self.__ordering_key(self.ordered_proofs[cur_idx]) == target_key
        ):
            first_match = cur_idx
            cur_idx -= 1
        return first_match

    def __find_size_start_idx(
        self,
        target_key: int,
        start: int,
        end: int,
    ) -> int:
        if end <= start:
            return end
        mid = (start + end) // 2
        maybe_match = self.__find_first_match(mid, target_key)
        if maybe_match:
            return maybe_match
        if target_key < self.__ordering_key(self.ordered_proofs[mid]):
            return self.__find_size_start_idx(target_key, start, mid)
        else:
            return self.__find_size_start_idx(target_key, mid + 1, end)

    @staticmethod
    def __get_dist(
        stripped1: StrippedProof, stripped2: StrippedProof
    ) -> Optional[float]:
        if (
            stripped1.file.file == stripped2.file.file
            and stripped1.line == stripped2.line
        ):
            return None  # same proof
        if stripped1.norm_steps and stripped2.norm_steps:
            raw_lev_dist = levenshtein_dist_fast(
                stripped1.norm_steps, stripped2.norm_steps
            )
            larger_len = max(len(stripped1.norm_steps), len(stripped2.norm_steps))
            return raw_lev_dist / larger_len
        return 1

    def __inspect_idx(
        self,
        q: list[SimilarProofCandidate],
        inspect_idx: int,
        target_proof: StrippedProof,
        n: int,
    ) -> Optional[list[SimilarProofCandidate]]:
        if inspect_idx < 0 or len(self.ordered_proofs) <= inspect_idx:
            return None
        inspect_proof = self.ordered_proofs[inspect_idx]
        inspect_key = self.__ordering_key(inspect_proof)
        target_key = self.__ordering_key(target_proof)
        lb = abs(inspect_key - target_key) / max(inspect_key, target_key)
        if n <= len(q) and q[0].score < lb:
            return None
        dist = self.__get_dist(target_proof, inspect_proof)
        if dist is None:
            return q
        heapq.heappush(q, SimilarProofCandidate(dist, inspect_proof))
        if len(q) > n:
            heapq.heappop(q)
        return q

    def nearest(self, new_stripped: StrippedProof) -> SimilarProofCandidate:
        nearest_one = self.nearest_n(new_stripped, n=1)
        assert len(nearest_one) == 1
        prf1_step_str = "".join(nearest_one[0].proof.steps)
        prf2_step_str = "".join(new_stripped.steps)
        if prf1_step_str == prf2_step_str:
            file_line1 = f"{new_stripped.file.file}:{new_stripped.line}"
            file_line2 = f"{nearest_one[0].proof.file.file}:{nearest_one[0].proof.line}"
            _logger.warning(f"Proofs from {file_line1} and {file_line2} are the same.")
        return nearest_one[0]

    def nearest_n(
        self, new_stripped: StrippedProof, n: int
    ) -> list[SimilarProofCandidate]:
        target_key = self.__ordering_key(new_stripped)
        _logger.debug("Finding start idx...")
        start_idx = self.__find_size_start_idx(
            target_key, 0, len(self.ordered_proofs) - 1
        )
        top_n: list[SimilarProofCandidate] = []
        _logger.debug("Inspecting start idx...")
        self.__inspect_idx(top_n, start_idx, new_stripped, n)
        step_forward = True
        step_back = True
        for i in range(1, len(self.ordered_proofs)):
            _logger.debug(f"Inspecting indices at len {i}...")
            if step_forward:
                f_idx = start_idx + i
                new_q = self.__inspect_idx(top_n, f_idx, new_stripped, n)
                if new_q is None:
                    step_forward = False
            if step_back:
                b_idx = start_idx - i
                new_q = self.__inspect_idx(top_n, b_idx, new_stripped, n)
                if new_q is None:
                    step_back = False
            if (not step_forward) and (not step_back):
                break
        return heapq.nlargest(n, top_n)

    def to_json(self) -> Any:
        return {"ordered_proofs": [p.to_json() for p in self.ordered_proofs]}

    def save(self, path: str) -> None:
        if os.path.exists(path):
            raise FileExistsError(path)
        dirname = os.path.dirname(path)
        os.makedirs(dirname, exist_ok=True)
        with open(path, "w") as fout:
            fout.write(json.dumps(self.to_json(), indent=2))

    @classmethod
    def load(cls, path: str) -> SortedProofs:
        with open(path, "r") as fin:
            return cls.from_json(json.load(fin))

    @classmethod
    def from_json(cls, json_data: Any) -> SortedProofs:
        ordered_proofs = [
            StrippedProof.from_json(p) for p in json_data["ordered_proofs"]
        ]
        return SortedProofs(ordered_proofs)

    @staticmethod
    def __ordering_key(s: StrippedProof) -> int:
        return len(s.steps)

    @staticmethod
    def get_stripped_proofs(
        data_split: DataSplit, split: Split, data_loc: str
    ) -> list[StrippedProof]:
        stripped_proofs: list[StrippedProof] = []
        print(f"Getting Proofs from {split2str(split)}...")
        for project in tqdm(data_split.get_project_list(split)):
            creation_time = project.get_creation_time(data_loc)
            for file_info in project.files:
                proofs = file_info.get_proofs(data_loc)
                for proof in proofs:
                    stripped_proofs.append(
                        StrippedProof.from_proof(proof, file_info, creation_time, split)
                    )
        return stripped_proofs

    @classmethod
    def create(cls, data_split: DataSplit, data_loc: str) -> SortedProofs:
        stripped_proofs = (
            cls.get_stripped_proofs(data_split, Split.TRAIN, data_loc)
            + cls.get_stripped_proofs(data_split, Split.VAL, data_loc)
            + cls.get_stripped_proofs(data_split, Split.TEST, data_loc)
        )
        print("Sorting Proofs...")
        return cls(sorted(stripped_proofs, key=cls.__ordering_key))


if __name__ == "__main__":
    parser = argparse.ArgumentParser("Create a proof distance search structure")
    parser.add_argument("data_split_loc", help="Location of a data split object.")
    parser.add_argument(
        "data_loc", help="Location of raw data with repos and datapoints."
    )
    parser.add_argument(
        "save_loc", help="Location to save the resulting data structure."
    )
    args = parser.parse_args(sys.argv[1:])
    data_split = DataSplit.load(args.data_split_loc)
    sorted_proofs = SortedProofs.create(data_split, args.data_loc)
    sorted_proofs.save(args.save_loc)
