from __future__ import annotations
from typing import Optional, Any

import sys
import os
import shutil
import argparse
from pathlib import Path
from dataclasses import dataclass
import json
import pickle
from queue import Queue

from data_management.samples import (
    ExampleSample,
    SelectedSteps,
    AllSteps,
    CertainSteps,
    load_sample,
)
from data_management.splits import Split, FileInfo, split_file_path
from data_management.sentence_db import SentenceDB
from data_management.jsonl_utils import shuffle, deduplicate
from premise_selection.rerank_example import RerankExample
from premise_selection.rerank_formatter import (
    RerankFormatter,
    RerankFormatterConf,
    rerank_conf_from_yaml,
    rerank_formatter_from_conf,
    close_rerank_formatter,
)
from util.constants import RERANK_DATA_CONF_NAME, CLEAN_CONFIG

import multiprocessing as mp


@dataclass
class RerankDatasetConf:
    n_procs: int
    train_sample_loc: Path
    val_sample_loc: Path
    test_sample_loc: Path
    sentence_db_loc: Path
    output_dataset_loc: Path
    rerank_formatter_conf: RerankFormatterConf

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> RerankDatasetConf:
        return cls(
            yaml_data["n_procs"],
            Path(yaml_data["train_sample_loc"]),
            Path(yaml_data["val_sample_loc"]),
            Path(yaml_data["test_sample_loc"]),
            Path(yaml_data["sentence_db_loc"]),
            Path(yaml_data["output_dataset_loc"]),
            rerank_conf_from_yaml(yaml_data["rerank_formatter"]),
        )


def writer(q: Queue[Optional[RerankExample]], out_file: str) -> None:
    num_examples_written = 0
    with open(out_file, "w") as fout:
        while True:
            example = q.get()
            match example:
                case RerankExample():
                    fout.write(json.dumps(example.to_json()) + "\n")
                    num_examples_written += 1
                    print(f"\rNum Examples: {num_examples_written}", end="")
                case None:
                    print()
                    return


def examples_to_queue(
    example_sample: ExampleSample,
    rerank_formatter_conf: RerankFormatterConf,
    file_info: FileInfo,
    sentence_db_loc: Path,
    selected_steps: SelectedSteps,
    q: Queue[Optional[RerankExample]],
) -> None:
    sentence_db = SentenceDB.load(sentence_db_loc)
    dp_obj = file_info.get_dp(example_sample.data_loc, sentence_db)
    rerank_formatter = rerank_formatter_from_conf(rerank_formatter_conf)
    match selected_steps:
        case AllSteps():
            for proof in dp_obj.proofs:
                for i in range(len(proof.steps)):
                    step = proof.steps[i]
                    examples = rerank_formatter.examples_from_step(
                        step,
                        proof,
                        dp_obj,
                    )
                    for example in examples:
                        q.put(example)
        case CertainSteps(steps=step_idxs):
            for step_idx in step_idxs:
                proof = dp_obj.proofs[step_idx.proof_idx]
                step = proof.steps[step_idx.step_idx]
                examples = rerank_formatter.examples_from_step(
                    step,
                    proof,
                    dp_obj,
                )
                for example in examples:
                    q.put(example)
    close_rerank_formatter(rerank_formatter)
    sentence_db.close()


__ArgTuple = tuple[
    ExampleSample,
    RerankFormatterConf,
    FileInfo,
    Path,
    SelectedSteps,
    Queue[Optional[RerankExample]],
]


def __get_split_transformation_args(
    example_sampler: ExampleSample,
    formatter_conf: RerankFormatterConf,
    sentence_db_loc: Path,
    q: Queue[RerankExample | None],
) -> list[__ArgTuple]:
    arg_list: list[__ArgTuple] = []
    for file, selected_steps in example_sampler.step_generator():
        arg_list.append(
            (
                example_sampler,
                formatter_conf,
                file,
                sentence_db_loc,
                selected_steps,
                q,
            )
        )
    return arg_list


def get_split_transformation_args(
    example_config: RerankDatasetConf,
    split: Split,
    q: Queue[Optional[RerankExample]],
) -> list[__ArgTuple]:
    match split:
        case Split.TRAIN:
            return __get_split_transformation_args(
                load_sample(example_config.train_sample_loc),
                example_config.rerank_formatter_conf,
                example_config.sentence_db_loc,
                q,
            )
        case Split.VAL:
            return __get_split_transformation_args(
                load_sample(example_config.val_sample_loc),
                example_config.rerank_formatter_conf,
                example_config.sentence_db_loc,
                q,
            )
        case Split.TEST:
            return __get_split_transformation_args(
                load_sample(example_config.test_sample_loc),
                example_config.rerank_formatter_conf,
                example_config.sentence_db_loc,
                q,
            )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "original_conf_loc", help="Location of the original configuration file"
    )
    args = parser.parse_args(sys.argv[1:])

    conf_path = Path(f"./{CLEAN_CONFIG}")
    assert conf_path.exists()
    with conf_path.open("rb") as fin:
        example_conf: RerankDatasetConf = pickle.load(fin)

    if example_conf.n_procs < 2:
        raise ValueError("Data processing needs at least 2 processes.")

    if os.path.exists(example_conf.output_dataset_loc):
        raise FileExistsError(f"{example_conf.output_dataset_loc}")
    os.makedirs(example_conf.output_dataset_loc)

    with mp.Manager() as manager:
        q: Queue[Optional[RerankExample]] = manager.Queue()
        with mp.Pool(example_conf.n_procs) as pool:
            for split in [Split.TEST, Split.VAL, Split.TRAIN]:
                split_args = get_split_transformation_args(example_conf, split, q)
                raw_path = split_file_path(
                    example_conf.output_dataset_loc,
                    split,
                    shuffled=False,
                    deduplicated=False,
                )
                deduped_path = split_file_path(
                    example_conf.output_dataset_loc,
                    split,
                    shuffled=False,
                    deduplicated=True,
                )
                shuffled_path = split_file_path(
                    example_conf.output_dataset_loc,
                    split,
                    shuffled=True,
                    deduplicated=True,
                )
                print(f"Processing {split.name}...")
                train_writer = pool.apply_async(writer, (q, raw_path))
                pool.starmap(examples_to_queue, split_args)
                q.put(None)
                train_writer.wait()
                # for args in split_args:
                #     examples_to_queue(*args)
                num_duplicates = deduplicate(raw_path, deduped_path)
                print(f"Num Duplicates: {num_duplicates}")
                os.remove(raw_path)
                shuffle(deduped_path, shuffled_path)
                os.remove(deduped_path)

    conf_out_loc = os.path.join(example_conf.output_dataset_loc, RERANK_DATA_CONF_NAME)
    shutil.copy(args.original_conf_loc, conf_out_loc)
