

from __future__ import annotations
from typing import Optional, Any
import sys, os
import shutil
import argparse
import multiprocessing as mp
from queue import Queue


import torch
from typeguard import typechecked
import json
from tqdm import tqdm
import yaml

from tactic_gen.lm_example import LmExample, BasicWholeProofFormatter
from data_management.splits import (
    FileInfo,
    Split,
    DataSplit,
    split_file_path,
)
from data_management.sentence_db import SentenceDB
from data_management.samples import (
    ExampleSample,
    load_sample,
    SelectedSteps,
    AllSteps,
    CertainSteps,
)
from data_management.jsonl_utils import shuffle, deduplicate
from util.util import get_basic_logger
from util.constants import DATA_CONF_NAME

_logger = get_basic_logger(__name__)


def writer(q: Queue[Optional[LmExample]], out_file: str) -> None:
    num_examples_written = 0
    with open(out_file, "w") as fout:
        while True:
            example = q.get()
            match example:
                case LmExample():
                    fout.write(json.dumps(example.to_json()) + "\n")
                    num_examples_written += 1
                    print(f"\rNum Examples: {num_examples_written}", end="")
                case None:
                    print()
                    return


def examples_to_queue(
    data_loc: str,
    formatter: BasicWholeProofFormatter,
    file_info: FileInfo,
    sentence_db_loc: str,
    q: Queue[Optional[LmExample]],
) -> None:
    sentence_db = SentenceDB.load(sentence_db_loc) 
    dp_obj = file_info.get_dp(data_loc, sentence_db)
    for proof in dp_obj.proofs:
        example = formatter.example_from_proof(proof)
        q.put(example)

__ArgTuple = tuple[
    str, BasicWholeProofFormatter, FileInfo, str, Queue[Optional[LmExample]]
]


def get_split_transformation_args(
    data_loc: str,
    data_split: DataSplit,
    split: Split,
    formatter: BasicWholeProofFormatter,
    sentence_db_loc: str,
    q: Queue[LmExample | None],
) -> list[__ArgTuple]:
    arg_list: list[__ArgTuple] = []
    for file in data_split.get_file_list(split):
        arg_list.append(
            (data_loc, formatter, file, sentence_db_loc, q)
        )
    return arg_list



if __name__ == "__main__":
    mp.set_start_method("spawn")
    parser = argparse.ArgumentParser(
        "Create a jsonl dataset from the data collected by the coq lsp."
    )
    parser.add_argument("data_loc", help="Location of raw dataset.")
    parser.add_argument("split_loc", help="Location of data split.")
    parser.add_argument("sentence_db_loc", help="Location of setntence db.")
    parser.add_argument("output_dataset_loc", help="Location to save the data.")
    parser.add_argument(
        "--num_procs",
        "-n",
        type=int,
        help="Number of processes to use to create the dataset.",
    )

    args = parser.parse_args(sys.argv[1:])
    num_procs = 1
    if args.num_procs:
        num_procs = args.num_procs
        if num_procs < 2:
            raise ValueError("Data processing needs at least 2 processes.")
        

    if os.path.exists(args.output_dataset_loc):
        raise FileExistsError(f"{args.output_dataset_loc}")
    os.makedirs(args.output_dataset_loc)

    with mp.Manager() as manager:
        q: Queue[Optional[LmExample]] = manager.Queue()
        with mp.Pool(num_procs) as pool:
            for split in [Split.TEST, Split.VAL, Split.TRAIN]:
                split_args = get_split_transformation_args(example_config, split, q)
                raw_path = split_file_path(
                    example_config.output_dataset_loc,
                    split,
                    shuffled=False,
                    deduplicated=False,
                )
                deduped_path = split_file_path(
                    example_config.output_dataset_loc,
                    split,
                    shuffled=False,
                    deduplicated=True,
                )
                shuffled_path = split_file_path(
                    example_config.output_dataset_loc,
                    split,
                    shuffled=True,
                    deduplicated=True,
                )
                print(f"Processing {split.name}...")
                train_writer = pool.apply_async(writer, (q, raw_path))
                pool.starmap(examples_to_queue, split_args)
                q.put(None)
                train_writer.wait()
                num_duplicates = deduplicate(raw_path, deduped_path)
                print(f"Num Duplicates: {num_duplicates}")
                os.remove(raw_path)
                shuffle(deduped_path, shuffled_path)
                os.remove(deduped_path)

    conf_out_loc = os.path.join(example_config.output_dataset_loc, DATA_CONF_NAME)
    shutil.copy(args.lm_data_config_loc, conf_out_loc)
