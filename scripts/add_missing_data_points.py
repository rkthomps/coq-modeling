import os
import argparse
import json
from pathlib import Path
from data_management.create_file_data_point import (
    get_data_point,
    get_switch_loc,
    NoProofsError,
)
from data_management.sentence_db import SentenceDB

from concurrent.futures import ProcessPoolExecutor, Future

import logging
from util.constants import RANGO_LOGGER

_logger = logging.getLogger(RANGO_LOGGER)

REPO_PATH = Path("raw-data/coq-dataset/repos")


def find_workspace(file_path: Path) -> Path:
    workspace_names = [
        "AbsInt-CompCert",
        "coq-community-coq-ext-lib",
        "coq-community-fourcolor",
        "coq-community-math-classes",
        "coq-community-reglang",
        "coq-community-buchberger",
        "coq-community-hoare-tut",
        "coq-community-zorns-lemma",
        "coq-community-huffman",
        "thery-PolTac",
        "coq-community-dblib",
        "coq-contribs-zfc",
    ]
    for w in workspace_names:
        w_path = REPO_PATH / w
        if file_path.resolve().is_relative_to(w_path.resolve()):
            return w_path
    raise ValueError(f"Could not find workspace for {file_path}")


def create_and_save_dp(
    file_path: Path, workspace_path: Path, sentence_db_loc: Path, save_loc: Path
) -> None:
    _logger.info(f"Creating data point for {file_path}")
    sentence_db = SentenceDB.load(sentence_db_loc)
    switch_loc = get_switch_loc()
    try:
        dp = get_data_point(
            file_path,
            workspace_path,
            sentence_db,
            add_to_dataset=True,
            switch_loc=switch_loc,
        )
        dp.save(save_loc / dp.dp_name, sentence_db, insert_allowed=False)
    except NoProofsError as e:
        _logger.warning(f"No proofs found for {file_path}: {e}")
    except Exception as e:
        _logger.error(f"Error with {file_path}: {e}")
    finally:
        sentence_db.close()


if __name__ == "__main__":
    from util.util import set_rango_logger

    set_rango_logger(__file__, logging.DEBUG)

    parser = argparse.ArgumentParser()
    parser.add_argument("--missing_files_loc", required=True)
    parser.add_argument("--sentence_db_loc", required=True)
    parser.add_argument("--save_loc", required=True)

    args = parser.parse_args()
    missing_files_loc = Path(args.missing_files_loc)
    sentence_db_loc = Path(args.sentence_db_loc)
    save_loc = Path(args.save_loc)

    assert missing_files_loc.exists()
    assert sentence_db_loc.exists()

    os.makedirs(save_loc, exist_ok=True)

    with missing_files_loc.open() as f:
        missing_files: list[str] = json.load(f)

    os_cpus = os.cpu_count()
    pool = ProcessPoolExecutor(max_workers=min(8, 1 if os_cpus is None else os_cpus))
    futures: list[Future] = []
    try:
        for mf in missing_files:
            f = pool.submit(
                create_and_save_dp,
                Path(mf),
                find_workspace(Path(mf)),
                sentence_db_loc,
                save_loc,
            )
            futures.append(f)

        for f in futures:
            f.result()
    finally:
        for f in futures:
            f.cancel()
