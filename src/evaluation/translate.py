from typing import Optional
from pathlib import Path
from dataclasses import dataclass
from enum import Enum

from coqstoq.check import Result
from coqstoq import get_theorem_list, Split
from coqstoq.eval_thms import EvalTheorem, get_file_hash, Position

import logging


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
    # Cutoff
    "Coq-BB5": "bb5",
    "PnVRocqLib": "pnvrocqlib",
    "semantic-preservation": "semantic-preservation",
}


@dataclass
class RawResult:
    project: str
    file_name: str
    thm_str: str
    success: bool
    time: float
    proof: Optional[str]


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


def get_candidate_ranges(r_result: RawResult, coqstoq_file: CoqStoqFile) -> list[Range]:
    start = 0
    ranges: list[Range] = []
    while r_result.thm_str in coqstoq_file.contents[start:]:
        next_idx = coqstoq_file.contents.find(r_result.thm_str, start)
        start_pos = idx_to_pos(next_idx, coqstoq_file.contents)
        end_pos_pre = idx_to_pos(
            next_idx + len(r_result.thm_str) - 1, coqstoq_file.contents
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


def get_theorem_possibilities(
    r_result: RawResult,
    raw_map: dict[Path, list[RawResult]],
) -> tuple[list[RawResult], int]:
    pbot_file_thms = raw_map[
        Path(project_name_map[r_result.project]) / r_result.file_name
    ]
    same_thms: list[RawResult] = []
    thm_pos: Optional[int] = None
    for i, thm in enumerate(pbot_file_thms):
        if r_result == thm:
            assert thm_pos is None
            thm_pos = len(same_thms)
            same_thms.append(thm)
        elif r_result.thm_str in thm.thm_str or thm.thm_str in r_result.thm_str:
            same_thms.append(thm)
    assert thm_pos is not None
    return same_thms, thm_pos


def map_filter_candidate_ranges(
    ranges: list[Range], coqstoq_file: CoqStoqFile
) -> list[EvalTheorem]:
    candidate_thms: list[EvalTheorem] = []
    for r in ranges:
        matching_thm: Optional[EvalTheorem] = None
        for thm in coqstoq_file.thms:
            if intersect(r, Range(thm.theorem_start_pos, thm.theorem_end_pos)):
                assert matching_thm is None
                matching_thm = thm
                candidate_thms.append(matching_thm)
    return candidate_thms


def raw_result_to_result(
    r_result: RawResult,
    coqstoq_files: dict[Path, CoqStoqFile],
    raw_map: dict[Path, list[RawResult]],
) -> Result | FailureMode:
    assert r_result.project in project_name_map, r_result
    p_target_file = Path(project_name_map[r_result.project]) / r_result.file_name
    if p_target_file not in coqstoq_files:
        logging.warning(f"Could not find {p_target_file} in coqstoq_files")
        return FailureMode.FILE_MISSING
    coqstoq_file = coqstoq_files[p_target_file]
    candidate_ranges = get_candidate_ranges(r_result, coqstoq_file)
    if 0 == len(candidate_ranges):
        logging.warning(f"Could not find theorem in {p_target_file}")
        return FailureMode.THM_MISSING

    candidate_thms = map_filter_candidate_ranges(candidate_ranges, coqstoq_file)
    single_thm: Optional[EvalTheorem] = None

    if 0 == len(candidate_thms):
        logging.warning(f"Theorem does not intersect with any thm in {p_target_file}")
        return FailureMode.THM_MISMATCH

    if 1 < len(candidate_thms):
        pbot_possibilities, thm_idx = get_theorem_possibilities(r_result, raw_map)
        if len(pbot_possibilities) != len(candidate_thms):
            logging.warning(f"Ambiguous theorem in {p_target_file}")
            # ipdb.set_trace()
            return FailureMode.AMBIGUOUS
        else:
            single_thm = candidate_thms[thm_idx]
    else:
        assert 1 == len(candidate_thms)
        single_thm = candidate_thms[0]
    return Result(single_thm, r_result.proof, r_result.time)


def get_raw_map(
    proverbot_results: list[RawResult],
) -> dict[Path, list[RawResult]]:
    proverbot_map: dict[Path, list[RawResult]] = {}
    for r in proverbot_results:
        r_file = Path(project_name_map[r.project]) / r.file_name
        if r_file not in proverbot_map:
            proverbot_map[r_file] = []
        proverbot_map[r_file].append(r)
    return proverbot_map


def get_save_loc(eval_save_loc: Path, eval_thm: EvalTheorem) -> Path:
    return (
        eval_save_loc
        / eval_thm.project.workspace.name
        / eval_thm.path
        / f"{eval_thm.theorem_start_pos.line}-{eval_thm.theorem_start_pos.column}.json"
    )


def raw_results_to_results(
    p_results: list[RawResult], coqstoq_loc: Path, split: Split
) -> list[Result]:
    coqstoq_files = get_coqstoq_files(coqstoq_loc, split)
    proverbot_map = get_raw_map(p_results)
    results: list[Result] = []
    file_missing = 0
    ambiguous = 0
    thm_missing = 0
    thm_mismatch = 0
    for p in p_results:
        result = raw_result_to_result(p, coqstoq_files, proverbot_map)
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


def get_raw_file_set(raw_results: list[RawResult]) -> set[str]:
    proverbot_files = set()
    for r in raw_results:
        proverbot_files.add(Path(project_name_map[r.project]) / r.file_name)
    return proverbot_files


def get_theorem_str(thm: EvalTheorem, file: CoqStoqFile) -> str:
    file_lines = file.contents.split("\n")
    theorem_lines = file_lines[
        thm.theorem_start_pos.line : thm.theorem_end_pos.line + 1
    ].copy()
    theorem_lines[-1] = theorem_lines[-1][: thm.theorem_end_pos.column]
    theorem_lines[0] = theorem_lines[0][thm.theorem_start_pos.column :]
    return "\n".join(theorem_lines)
