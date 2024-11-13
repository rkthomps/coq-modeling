from __future__ import annotations
import argparse
import os
import json
from enum import Enum
from pathlib import Path
from dataclasses import dataclass
from typing import Optional, Any

from coqstoq.check import Result
from coqstoq.eval_thms import EvalTheorem, get_file_hash, Position
from coqstoq import get_theorem_list, Split

import logging


@dataclass
class ProverBotResult:
    project: str
    file_name: str
    thm_str: str
    module: list[str]
    success: bool
    time: float
    num_steps: int
    proof: Optional[str]

    META_IDX = 0
    META_PROJ_IDX = 0
    META_FILE_IDX = 1
    META_MODULE_IDX = 2
    META_THM_IDX = 3

    PROOF_IDX = 1

    @classmethod
    def proof_from_cmds(cls, commands: list[Any]) -> str:
        tactics = [c["tactic"] for c in commands]
        return "\n".join(tactics)

    @classmethod
    def from_json(cls, json_data: Any) -> ProverBotResult:
        metadata_json = json_data[cls.META_IDX]
        proj = metadata_json[cls.META_PROJ_IDX]
        file = metadata_json[cls.META_FILE_IDX]
        thm = metadata_json[cls.META_THM_IDX]
        module = metadata_json[cls.META_MODULE_IDX]
        assert 0 < len(module) and module.endswith(".")
        module_list_w_filename = module[:-1].split(".")
        assert 0 < len(module_list_w_filename)
        module_list = module_list_w_filename[1:]

        proof_json = json_data[cls.PROOF_IDX]
        success = proof_json["status"] == "SUCCESS"
        if (
            not success
            and proof_json["status"] != "INCOMPLETE"
            and proof_json["status"] != "FAILURE"
            and proof_json["status"] != "CRASHED"
        ):
            print(json.dumps(json_data, indent=2))
            exit()
        proof = cls.proof_from_cmds(proof_json["commands"]) if success else None

        time = proof_json["time_taken"]
        steps = proof_json["steps_taken"]
        return cls(proj, file, thm, module_list, success, time, steps, proof)


def results_from_file(file_path: Path) -> list[ProverBotResult]:
    file_results: list[ProverBotResult] = []
    with file_path.open() as fin:
        for line in fin:
            line_info = json.loads(line)
            file_results.append(ProverBotResult.from_json(line_info))
    return file_results


def load_proverbot_results(path: Path) -> list[ProverBotResult]:
    results: list[ProverBotResult] = []
    for root, _, files in os.walk(path):
        for file in files:
            if file.endswith("proofs.txt"):
                results.extend(results_from_file(Path(root) / file))
    return results


@dataclass
class CoqStoqFile:
    contents: str
    thms: list[EvalTheorem]


project_name_map: dict[str, str] = {
    ".": "compcert",
    "AbsInt-CompCert": "compcert",
    "coq-community-buchberger": "buchberger",
    "coq-community-coq-ext-lib": "ext-lib",
    "coq-community-dblib": "dblib",
    "coq-community-fourcolor": "fourcolor",
    "coq-community-hoare-tut": "hoare-tut",
    "coq-community-huffman": "huffman",
    "coq-community-math-classes": "math-classes",
    "coq-community-reglang": "reglang",
    "coq-community-zorns-lemma": "zorns-lemma",
    "coq-contribs-zfc": "zfc",
    "thery-PolTac": "poltac",
}


def get_coqstoq_files(coqstoq_loc: Path, split: Split) -> dict[Path, CoqStoqFile]:
    thms = get_theorem_list(split, coqstoq_loc)
    content_dict: dict[Path, str] = {}
    thms_dict: dict[Path, list[EvalTheorem]] = {}
    for thm in thms:
        thm_path = Path(thm.project.workspace.name) / thm.path
        if thm_path not in content_dict:
            assert thm_path not in thms_dict
            real_thm_path = coqstoq_loc / thm.project.workspace / thm.path
            assert get_file_hash(real_thm_path) == thm.hash
            contents = real_thm_path.read_text()
            content_dict[thm_path] = contents
            thms_dict[thm_path] = []
        thms_dict[thm_path].append(thm)

    coqstoq_dict: dict[Path, CoqStoqFile] = {}
    for k, v in content_dict.items():
        coqstoq_dict[k] = CoqStoqFile(v, thms_dict[k])

    print(len(coqstoq_dict), len(content_dict), len(thms_dict))
    assert len(coqstoq_dict) == len(content_dict)
    assert len(content_dict) == len(thms_dict)
    return coqstoq_dict


@dataclass
class Range:
    start: Position
    end: Position


def idx_to_pos(idx: int, s: str) -> Position:
    prefix = s[: (idx + 1)]
    prefix_lines = prefix.split("\n")
    return Position(len(prefix_lines) - 1, len(prefix_lines[-1]) - 1)


assert idx_to_pos(3, "a\nbc") == Position(1, 1)


def get_candidate_ranges(
    p_result: ProverBotResult, coqstoq_file: CoqStoqFile
) -> list[Range]:
    start = 0
    ranges: list[Range] = []
    while p_result.thm_str in coqstoq_file.contents[start:]:
        next_idx = coqstoq_file.contents.find(p_result.thm_str, start)
        start_pos = idx_to_pos(next_idx, coqstoq_file.contents)
        end_pos_pre = idx_to_pos(
            next_idx + len(p_result.thm_str) - 1, coqstoq_file.contents
        )
        end_pos = Position(end_pos_pre.line, end_pos_pre.column + 1)
        ranges.append(Range(start_pos, end_pos))
        start = next_idx + 1
    return ranges


def intersect_helper(r1: Range, r2: Range) -> bool:
    assert r1.start.line <= r2.start.line
    if r1.start.line == r2.start.line:
        assert r1.start.column <= r2.start.column
    if r1.end.line == r2.start.line:
        return r2.start.column < r1.end.column
    return r2.start.line < r1.end.line


def intersect(r1: Range, r2: Range) -> bool:
    if r1.start.line == r2.start.line:
        if r2.start.column < r1.start.column:
            return intersect_helper(r2, r1)
        else:
            return intersect_helper(r1, r2)

    if r1.start.line < r2.start.line:
        return intersect_helper(r1, r2)

    return intersect_helper(r2, r1)


assert intersect(
    Range(Position(0, 0), Position(0, 1)), Range(Position(0, 0), Position(0, 2))
)
assert intersect(
    Range(Position(0, 0), Position(1, 2)), Range(Position(1, 1), Position(3, 2))
)
assert not intersect(
    Range(Position(0, 0), Position(1, 2)), Range(Position(1, 2), Position(3, 2))
)
assert intersect(
    Range(Position(0, 0), Position(0, 2)), Range(Position(0, 0), Position(0, 1))
)
assert intersect(
    Range(Position(1, 1), Position(3, 2)), Range(Position(0, 0), Position(1, 2))
)
assert not intersect(
    Range(Position(1, 2), Position(3, 2)), Range(Position(0, 0), Position(1, 2))
)


class FailureMode(Enum):
    FILE_MISSING = 0
    AMBIGUOUS = 1
    THM_MISSING = 2
    THM_MISMATCH = 3


def proverbot_result_to_result(
    p_result: ProverBotResult, coqstoq_files: dict[Path, CoqStoqFile]
) -> Result | FailureMode:
    assert p_result.project in project_name_map, p_result
    p_target_file = Path(project_name_map[p_result.project]) / p_result.file_name
    if p_target_file not in coqstoq_files:
        logging.warning(f"Could not find {p_target_file} in coqstoq_files")
        return FailureMode.FILE_MISSING
    coqstoq_file = coqstoq_files[p_target_file]
    candidate_ranges = get_candidate_ranges(p_result, coqstoq_file)
    if 1 < len(candidate_ranges):
        logging.warning(f"Ambiguous theorem in {p_target_file}")
        return FailureMode.AMBIGUOUS
    if 0 == len(candidate_ranges):
        logging.warning(f"Could not find theorem in {p_target_file}")
        return FailureMode.THM_MISSING
    single_range = candidate_ranges[0]
    for thm in coqstoq_file.thms:
        if intersect(single_range, Range(thm.theorem_start_pos, thm.theorem_end_pos)):
            return Result(thm, p_result.proof, p_result.time)
    # logging.warning(f"Theorem does not intersect with any thm in {p_target_file}")
    return FailureMode.THM_MISMATCH


def proverbot_results_to_results(
    p_results: list[ProverBotResult], coqstoq_loc: Path, split: Split
) -> list[Result]:
    coqstoq_files = get_coqstoq_files(coqstoq_loc, split)
    results: list[Result] = []
    file_missing = 0
    ambiguous = 0
    thm_missing = 0
    thm_mismatch = 0
    for p in p_results:
        result = proverbot_result_to_result(p, coqstoq_files)
        match result:
            case Result():
                results.append(result)
            case FailureMode.FILE_MISSING:
                file_missing += 1
            case FailureMode.AMBIGUOUS:
                ambiguous += 1
            case FailureMode.THM_MISSING:
                thm_missing += 1
            case FailureMode.THM_MISMATCH:
                thm_mismatch += 1
    print("File missing", file_missing)
    print("Ambiguous", ambiguous)
    print("Thm missing", thm_missing)
    print("Thm mismatch", thm_mismatch)
    print("Total", len(p_results))
    return results


def get_coqstoq_split(choice: str) -> Split:
    match choice:
        case "val":
            return Split.VAL
        case "test":
            return Split.TEST
        case "cutoff":
            return Split.CUTOFF
        case _:
            raise ValueError(f"Invalid choice: {choice}")


def get_thm_hash(thm: EvalTheorem) -> str:
    return f"{thm.project.workspace.name}/{thm.path}/{thm.theorem_start_pos.line}-{thm.theorem_start_pos.column}"


def get_proverbot_file_set(proverbot_results: list[ProverBotResult]) -> set[str]:
    proverbot_files = set()
    for r in proverbot_results:
        proverbot_files.add(Path(project_name_map[r.project]) / r.file_name)
    return proverbot_files


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--proverbot_loc", type=str, required=True)
    parser.add_argument("--coqstoq_loc", type=str, required=True)
    parser.add_argument(
        "--split", type=str, required=True, choices=["val", "test", "cutoff"]
    )
    parser.add_argument("--save_loc", type=str, required=True)

    args = parser.parse_args()
    proverbot_results = load_proverbot_results(Path(args.proverbot_loc))
    results = proverbot_results_to_results(
        proverbot_results, Path(args.coqstoq_loc), Split.TEST
    )
    print("Num not none", len(results))
    result_thms = set([get_thm_hash(r.thm) for r in results])
    print("Set size", len(result_thms))

    # find missing
    thms = get_theorem_list(get_coqstoq_split(args.split), Path(args.coqstoq_loc))
    print("Num coqstoq theorems", len(thms))
    proverbot_files = get_proverbot_file_set(proverbot_results)
    because_file_missing = 0
    total = 0
    missing_files: set[Path] = set()
    for t in thms:
        if get_thm_hash(t) not in result_thms:
            if Path(t.project.workspace.name) / t.path not in proverbot_files:
                because_file_missing += 1
                missing_files.add(Path(t.project.workspace.name) / t.path)
            total += 1

    print("Because file missing", because_file_missing)
    print("Missing", total)
    for f in sorted(list(missing_files)):
        print(f)
