from __future__ import annotations
from typeguard import typechecked
from typing import Any, Optional

import sys, os
import json
import shutil
import argparse
from queue import Queue
import multiprocessing as mp
import logging

from yaml import load, Loader

from premise_selection.premise_formatter import (
    PREMISE_ALIASES,
    CONTEXT_ALIASES,
    ContextFormat,
    PremiseFormat,
)
from premise_selection.premise_filter import PremiseFilter
from premise_selection.premise_example import PremiseTrainingExample
from premise_selection.create_premise_example import premise_training_examples_from_step
from model_deployment.premise_model_wrapper import (
    LocalPremiseModelWrapper,
    premise_wrapper_from_conf,
    move_prem_wrapper_to,
)
from data_management.splits import (
    FileInfo,
    DataSplit,
    Split,
    split_file_path,
)
from data_management.jsonl_utils import shuffle, deduplicate
from data_management.sentence_db import SentenceDB
from util.constants import PREMISE_DATA_CONF_NAME
from util.util import LOGGER
import torch


class PremiseDataConfig:
    def __init__(
        self,
        data_split: DataSplit,
        data_loc: str,
        sentence_db_loc: str,
        output_dataset_loc: str,
        base: LocalPremiseModelWrapper,
        num_negatives: int,
    ) -> None:
        self.data_split = data_split
        self.data_loc = data_loc
        self.sentence_db_loc = sentence_db_loc
        self.output_dataset_loc = output_dataset_loc
        self.base = base
        self.num_negatives = num_negatives

    @classmethod
    def from_config(cls, config: Any) -> PremiseDataConfig:
        data_split = DataSplit.load(config["data_split"])
        data_loc = config["data_loc"]
        sentence_db_loc = config["sentence_db_loc"]
        output_dataset_loc = config["output_dataset_loc"]
        base = premise_wrapper_from_conf(config["base_wrapper"])
        num_negatives = config["num_negatives"]
        return cls(
            data_split,
            data_loc,
            sentence_db_loc,
            output_dataset_loc,
            base,
            num_negatives,
        )


def get_examples_from_file(
    file_info: FileInfo,
    split: Split,
    premise_conf: PremiseDataConfig,
    device_idx: int,
    q: Queue[Optional[PremiseTrainingExample]],
) -> None:
    move_prem_wrapper_to(premise_conf.base, f"cuda:{device_idx}")
    sentence_db = SentenceDB.load(premise_conf.sentence_db_loc)
    try:
        file_obj = file_info.get_dp(premise_conf.data_loc, sentence_db)
    except FileNotFoundError:
        LOGGER.error(f"Could not find file: {file_info.file}")
        return
    for proof in file_obj.proofs:
        for step in proof.steps:
            step_examples = premise_training_examples_from_step(
                step,
                proof,
                file_obj,
                premise_conf.num_negatives,
                premise_conf.base,
            )
            for example in step_examples:
                q.put(example)
    sentence_db.close()


PremiseArgs = tuple[
    FileInfo, Split, PremiseDataConfig, int, Queue[Optional[PremiseTrainingExample]]
]


def get_dataset_args(
    premise_conf: PremiseDataConfig,
    split: Split,
    q: Queue[Optional[PremiseTrainingExample]],
) -> list[PremiseArgs]:
    num_devices = torch.cuda.device_count()
    argument_list: list[PremiseArgs] = []
    for project in premise_conf.data_split.get_project_list(split):
        for i, file in enumerate(project.files):
            argument_list.append((file, split, premise_conf, i % num_devices, q))
    return argument_list


def writer(q: Queue[Optional[PremiseTrainingExample]], out_file: str) -> None:
    num_examples_written = 0
    LOGGER.debug(f"Opening {out_file}")
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
    mp.set_start_method("spawn")
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
