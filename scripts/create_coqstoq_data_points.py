import os
import argparse
from pathlib import Path
from dataclasses import dataclass
from coqstoq import get_theorem_list, Split
from coqstoq.eval_thms import EvalTheorem, get_file_hash

from data_management.sentence_db import SentenceDB
from data_management.create_file_data_point import get_data_point, get_switch_loc

import logging
from util.util import set_rango_logger
from util.constants import RANGO_LOGGER

from coqpyt.lsp.structs import ResponseError

_logger = logging.getLogger(RANGO_LOGGER)


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


def get_files(thms: list[EvalTheorem]) -> set[Path]:
    files: set[Path] = set()
    for thm in thms:
        files.add(thm.path)
    return files


@dataclass(unsafe_hash=True)
class CoqStoqFile:
    path: Path
    workspace: Path


def get_coqstoq_file(thm: EvalTheorem, coqstoq_loc: Path) -> CoqStoqFile:
    path = coqstoq_loc / thm.project.workspace / thm.path
    assert get_file_hash(path) == thm.hash
    return CoqStoqFile(
        path,
        coqstoq_loc / thm.project.workspace,
    )


def get_coqstoq_files(
    thms: list[EvalTheorem], coqstoq_loc: Path
) -> set[CoqStoqFile]:
    files: set[CoqStoqFile] = set()
    for thm in thms:
        files.add(get_coqstoq_file(thm, coqstoq_loc))
    return files


def get_coqstoq_data_point(f: CoqStoqFile, sentence_db: SentenceDB, save_loc: Path):
    add_to_dataset = True
    switch_loc = get_switch_loc()
    compile_timeout = 6000
    try:
        dp = get_data_point(
            f.path,
            f.workspace,
            sentence_db,
            add_to_dataset,
            switch_loc,
            compile_timeout,
        )
        dp.save(save_loc / dp.dp_name, sentence_db, insert_allowed=True)
    except ResponseError as e:
        _logger.info(f"Failed to create data point for {f}: {e}")
    except Exception as e:
        _logger.error(f"Failed to create data point for {f}: {e}")


def get_predicted_dp_name(f: CoqStoqFile) -> str:
    return str(Path(f.workspace.name) / f.path.relative_to(f.workspace)).replace(
        "/", "-"
    )


if __name__ == "__main__":
    set_rango_logger(__file__, logging.INFO)
    parser = argparse.ArgumentParser()
    parser.add_argument("coqstoq_loc")
    parser.add_argument("split")
    parser.add_argument("save_loc")
    parser.add_argument("sentence_db_loc")

    args = parser.parse_args()
    coqstoq_loc = Path(args.coqstoq_loc)
    assert coqstoq_loc.exists()
    coqstoq_split: str = args.split
    sentence_db_loc = Path(args.sentence_db_loc)
    save_loc = Path(args.save_loc)

    if sentence_db_loc.exists():
        sentence_db = SentenceDB.load(sentence_db_loc)
    else:
        sentence_db = SentenceDB.create(sentence_db_loc)

    if not save_loc.exists():
        save_loc.mkdir(parents=True)

    theorem_list = get_theorem_list(coqstoq_split, coqstoq_loc)
    files = get_coqstoq_files(theorem_list, coqstoq_loc)
    for f in files:
        predicted_dp_name = get_predicted_dp_name(f)
        if os.path.exists(save_loc / predicted_dp_name):
            _logger.info(f"Skipping {f}")
            continue
        _logger.info(f"Processing {f}")
        get_coqstoq_data_point(f, sentence_db, save_loc)
