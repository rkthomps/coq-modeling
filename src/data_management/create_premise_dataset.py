from __future__ import annotations
from typing import Any, Optional

import sys, os
import json
import shutil
import argparse
from pathlib import Path
from queue import Queue
import multiprocessing as mp
from dataclasses import dataclass

from yaml import load, Loader

from premise_selection.premise_formatter import (
    PREMISE_ALIASES,
    CONTEXT_ALIASES,
)
from premise_selection.premise_example import PremiseTrainingExample
from premise_selection.premise_filter import PremiseFilter, PremiseFilterConf
from premise_selection.premise_formatter import PREMISE_ALIASES, CONTEXT_ALIASES
from data_management.splits import (
    FileInfo,
    DataSplit,
    Split,
    split_file_path,
)
from data_management.jsonl_utils import shuffle, deduplicate
from data_management.sentence_db import SentenceDB
from util.util import get_basic_logger
from util.constants import PREMISE_DATA_CONF_NAME


_logger = get_basic_logger(__name__)


@dataclass
class SelectDataConfig:
    n_procs: int
    data_split_loc: Path
    data_loc: Path
    sentence_db_loc: Path
    output_dataset_loc: Path
    num_negatives_per_positive: int
    num_in_file_negatives_per_positive: int
    context_format_type_alias: str
    premise_format_type_alias: str
    premise_filter_conf: PremiseFilterConf

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> SelectDataConfig:
        return cls(
            yaml_data["n_procs"],
            Path(yaml_data["data_split_loc"]),
            Path(yaml_data["data_loc"]),
            Path(yaml_data["sentence_db_loc"]),
            Path(yaml_data["output_dataset_loc"]),
            yaml_data["num_negatives_per_positive"],
            yaml_data["num_in_file_negatives_per_positive"],
            yaml_data["context_format_type_alias"],
            yaml_data["premise_format_type_alias"],
            PremiseFilterConf.from_yaml(yaml_data["premise_filter"]),
        )


def get_examples_from_file(
    file_info: FileInfo,
    split: Split,
    premise_conf: SelectDataConfig,
    q: Queue[Optional[PremiseTrainingExample]],
) -> None:
    sentence_db = SentenceDB.load(premise_conf.sentence_db_loc)
    try:
        file_obj = file_info.get_dp(premise_conf.data_loc, sentence_db)
    except FileNotFoundError:
        _logger.error(f"Could not find file: {file_info.file}")
        return
    premise_format_type = PREMISE_ALIASES[premise_conf.premise_format_type_alias]
    contex_format_type = CONTEXT_ALIASES[premise_conf.context_format_type_alias]
    filter = PremiseFilter.from_conf(premise_conf.premise_filter_conf)
    for proof in file_obj.proofs:
        for step in proof.steps:
            step_examples = PremiseTrainingExample.from_focused_step(
                step,
                proof,
                file_obj,
                premise_conf.num_negatives_per_positive,
                premise_conf.num_in_file_negatives_per_positive,
                contex_format_type,
                premise_format_type,
                filter,
            )
            for example in step_examples:
                q.put(example)


PremiseArgs = tuple[
    FileInfo, Split, SelectDataConfig, Queue[Optional[PremiseTrainingExample]]
]


def get_dataset_args(
    premise_conf: SelectDataConfig,
    split: Split,
    q: Queue[Optional[PremiseTrainingExample]],
) -> list[PremiseArgs]:
    argument_list: list[PremiseArgs] = []
    data_split = DataSplit.load(premise_conf.data_split_loc)
    for project in data_split.get_project_list(split):
        for file in project.files:
            argument_list.append((file, split, premise_conf, q))
    return argument_list


def writer(q: Queue[Optional[PremiseTrainingExample]], out_file: str) -> None:
    num_examples_written = 0
    _logger.debug(f"Opening {out_file}")
    with open(out_file, "w") as fout:
        while True:
            example = q.get()
            match example:
                case PremiseTrainingExample():
                    fout.write(json.dumps(example.to_json()) + "\n")
                    num_examples_written += 1
                    print(f"\rNum Examples: {num_examples_written}", end="")
                case None:
                    print()
                    return


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description=(
            "Create a jsonl dataset from the data " "collected by the coq lsp."
        )
    )
    parser.add_argument(
        "yaml_config",
        help=("Configuration file for creating the premise " "selection dataset."),
    )

    args = parser.parse_args(sys.argv[1:])

    with open(args.yaml_config, "r") as fin:
        conf = load(fin, Loader=Loader)

    premise_config = SelectDataConfig.from_yaml(conf)

    if premise_config.n_procs < 2:
        raise ValueError("Data processing needs at least 2 processes.")

    if os.path.exists(premise_config.output_dataset_loc):
        raise FileExistsError(f"{premise_config.output_dataset_loc}")
    os.makedirs(premise_config.output_dataset_loc)

    with mp.Manager() as manager:
        q: Queue[Optional[PremiseTrainingExample]] = manager.Queue()
        with mp.Pool(premise_config.n_procs) as pool:
            for split in [Split.TEST, Split.VAL, Split.TRAIN]:
                split_args = get_dataset_args(premise_config, split, q)
                raw_path = split_file_path(
                    premise_config.output_dataset_loc,
                    split,
                    shuffled=False,
                    deduplicated=False,
                )
                deduped_path = split_file_path(
                    premise_config.output_dataset_loc,
                    split,
                    shuffled=False,
                    deduplicated=True,
                )
                shuffled_path = split_file_path(
                    premise_config.output_dataset_loc,
                    split,
                    shuffled=True,
                    deduplicated=True,
                )
                print(f"Processing {split.name}...")
                train_writer = pool.apply_async(writer, (q, raw_path))
                pool.starmap(get_examples_from_file, split_args)
                q.put(None)
                train_writer.wait()
                num_duplicates = deduplicate(raw_path, deduped_path)
                print(f"Num Duplicates: {num_duplicates}")
                os.remove(raw_path)
                shuffle(deduped_path, shuffled_path)
                os.remove(deduped_path)

    config_destination = os.path.join(
        premise_config.output_dataset_loc, PREMISE_DATA_CONF_NAME
    )
    shutil.copy(args.yaml_config, config_destination)
