from __future__ import annotations
from typeguard import typechecked
from typing import Any, Optional

import sys, os
import json
import shutil
import argparse
from queue import Queue
import multiprocessing as mp

from yaml import load, Loader

from premise_selection.premise_formatter import (
    PREMISE_ALIASES,
    CONTEXT_ALIASES,
    ContextFormat,
    PremiseFormat,
)
from premise_selection.premise_example import PremiseTrainingExample
from premise_selection.premise_filter import PremiseFilter
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


@typechecked
class PremiseDataConfig:
    def __init__(
        self,
        data_split: DataSplit,
        data_loc: str,
        sentence_db_loc: str, 
        output_dataset_loc: str,
        num_negatives_per_positive: int,
        num_in_file_negatives_per_positive: int,
        context_format_type: type[ContextFormat],
        premise_format_type: type[PremiseFormat],
        premise_filter: PremiseFilter,
    ) -> None:
        self.data_split = data_split
        self.data_loc = data_loc
        self.sentence_db_loc = sentence_db_loc
        self.output_dataset_loc = output_dataset_loc
        self.num_negatives_per_positive = num_negatives_per_positive
        self.num_in_file_negatives_per_positive = num_in_file_negatives_per_positive
        self.context_format_type = context_format_type
        self.premise_format_type = premise_format_type
        self.premise_filter = premise_filter

    @classmethod
    def from_config(cls, config: Any) -> PremiseDataConfig:
        data_split = DataSplit.load(config["data_split"])
        data_loc = config["data_loc"]
        sentence_db_loc = config["sentence_db_loc"]
        output_dataset_loc = config["output_dataset_loc"]
        num_negatives_per_positive = config["num_negatives_per_positive"]
        num_in_file_negatives_per_positive = config[
            "num_in_file_negatives_per_positive"
        ]
        context_format_alias = config["context_format_alias"]
        context_format_type = CONTEXT_ALIASES[context_format_alias]
        premise_format_alias = config["premise_format_alias"]
        premise_format_type = PREMISE_ALIASES[premise_format_alias]
        premise_filter = PremiseFilter.from_json(config["premise_filter"])
        return cls(
            data_split,
            data_loc,
            sentence_db_loc,
            output_dataset_loc,
            num_negatives_per_positive,
            num_in_file_negatives_per_positive,
            context_format_type,
            premise_format_type,
            premise_filter,
        )


def get_examples_from_file(
    file_info: FileInfo,
    split: Split,
    premise_conf: PremiseDataConfig,
    q: Queue[Optional[PremiseTrainingExample]],
) -> None:
    sentence_db = SentenceDB.load(premise_conf.sentence_db_loc)
    try:
        file_obj = file_info.get_dp(premise_conf.data_loc, sentence_db)
    except FileNotFoundError:
        _logger.error(f"Could not find file: {file_info.file}")
        return
    for proof in file_obj.proofs:
        for step in proof.steps:
            step_examples = PremiseTrainingExample.from_focused_step(
                step,
                proof,
                file_obj,
                premise_conf.num_negatives_per_positive,
                premise_conf.num_in_file_negatives_per_positive,
                premise_conf.context_format_type,
                premise_conf.premise_format_type,
                premise_conf.premise_filter,
                split,
            )
            for example in step_examples:
                q.put(example)


PremiseArgs = tuple[
    FileInfo, Split, PremiseDataConfig, Queue[Optional[PremiseTrainingExample]]
]


def get_dataset_args(
    premise_conf: PremiseDataConfig,
    split: Split,
    q: Queue[Optional[PremiseTrainingExample]],
) -> list[PremiseArgs]:
    argument_list: list[PremiseArgs] = []
    for project in premise_conf.data_split.get_project_list(split):
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
    parser.add_argument(
        "--num_procs",
        "-n",
        type=int,
        help="Number of processes to use to create the dataset.",
    )

    args = parser.parse_args(sys.argv[1:])
    num_procs = 2
    if args.num_procs:
        num_procs = args.num_procs
        if num_procs < 2:
            raise ValueError("Data processing needs at least 2 processes.")

    with open(args.yaml_config, "r") as fin:
        conf = load(fin, Loader=Loader)

    premise_config = PremiseDataConfig.from_config(conf)

    if os.path.exists(premise_config.output_dataset_loc):
        raise FileExistsError(f"{premise_config.output_dataset_loc}")
    os.makedirs(premise_config.output_dataset_loc)

    with mp.Manager() as manager:
        q: Queue[Optional[PremiseTrainingExample]] = manager.Queue()
        with mp.Pool(num_procs) as pool:
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
