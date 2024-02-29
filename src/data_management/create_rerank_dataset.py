from __future__ import annotations
from typing import Optional, Any

import sys
import os
import shutil
import argparse
import json
import yaml
from queue import Queue
from typeguard import typechecked
import torch

from data_management.samples import (
    ExampleSample,
    SelectedSteps,
    AllSteps,
    CertainSteps,
    load_sample,
)
from data_management.splits import DataSplit, Split, FileInfo, split_file_path
from data_management.jsonl_utils import shuffle, deduplicate
from premise_selection.rerank_example import RerankExample
from premise_selection.rerank_formatter import RerankFormatter
from util.constants import RERANK_DATA_CONF_NAME

import multiprocessing as mp


@typechecked
class ReRankExampleConfig:
    FORMATTER_KEY = "rerank_formatter"

    def __init__(
        self,
        train_sample: ExampleSample,
        val_sample: ExampleSample,
        test_sample: ExampleSample,
        output_dataset_loc: str,
        rerank_formatter: RerankFormatter,
    ) -> None:
        self.train_sample = train_sample
        self.val_sample = val_sample
        self.test_sample = test_sample
        self.output_dataset_loc = output_dataset_loc
        self.rerank_formatter = rerank_formatter

    @classmethod
    def from_config(cls, config: Any) -> ReRankExampleConfig:
        train_sample_loc = config["train_sample_loc"]
        train_sample = load_sample(train_sample_loc)
        val_sample_loc = config["val_sample_loc"]
        val_sample = load_sample(val_sample_loc)
        test_sample_loc = config["test_sample_loc"]
        test_sample = load_sample(test_sample_loc)
        output_dataset_loc = config["output_dataset_loc"]
        rerank_formatter = RerankFormatter.from_conf(config["rerank_formatter"])
        return cls(
            train_sample,
            val_sample,
            test_sample,
            output_dataset_loc,
            rerank_formatter,
        )

    @classmethod
    def load(cls, path: str) -> ReRankExampleConfig:
        with open(path, "r") as fin:
            yaml_conf = yaml.load(fin, Loader=yaml.Loader)
        return cls.from_config(yaml_conf)


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
    rerank_formatter: RerankFormatter,
    file_info: FileInfo,
    selected_steps: SelectedSteps,
    device_idx: int,
    q: Queue[Optional[RerankExample]],
) -> None:
    cuda_str = f"cuda:{device_idx}"
    rerank_formatter.move_to(cuda_str)
    dp_obj = file_info.get_dp(example_sample.data_loc)
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


__ArgTuple = tuple[
    ExampleSample,
    RerankFormatter,
    FileInfo,
    SelectedSteps,
    int,
    Queue[Optional[RerankExample]],
]


def __get_split_transformation_args(
    example_sampler: ExampleSample,
    formatter: RerankFormatter,
    q: Queue[RerankExample | None],
) -> list[__ArgTuple]:
    num_devices = torch.cuda.device_count()
    arg_list: list[__ArgTuple] = []
    for i, (file, selected_steps) in enumerate(example_sampler.step_generator()):
        device_idx = i % num_devices
        arg_list.append(
            (
                example_sampler,
                formatter,
                file,
                selected_steps,
                device_idx,
                q,
            )
        )
    return arg_list


def get_split_transformation_args(
    example_config: ReRankExampleConfig,
    split: Split,
    q: Queue[Optional[RerankExample]],
) -> list[__ArgTuple]:
    match split:
        case Split.TRAIN:
            return __get_split_transformation_args(
                example_config.train_sample,
                example_config.rerank_formatter,
                q,
            )
        case Split.VAL:
            return __get_split_transformation_args(
                example_config.val_sample,
                example_config.rerank_formatter,
                q,
            )
        case Split.TEST:
            return __get_split_transformation_args(
                example_config.test_sample,
                example_config.rerank_formatter,
                q,
            )


if __name__ == "__main__":
    mp.set_start_method("spawn")
    parser = argparse.ArgumentParser(
        "Create a jsonl dataset to rerank premises selected by the given model."
    )
    parser.add_argument(
        "rerank_data_config_loc",
        help="Location of configuration file for LmExample dataset.",
    )
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

    example_config = ReRankExampleConfig.load(args.rerank_data_config_loc)

    if os.path.exists(example_config.output_dataset_loc):
        raise FileExistsError(f"{example_config.output_dataset_loc}")
    os.makedirs(example_config.output_dataset_loc)

    with mp.Manager() as manager:
        q: Queue[Optional[RerankExample]] = manager.Queue()
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

    conf_out_loc = os.path.join(
        example_config.output_dataset_loc, RERANK_DATA_CONF_NAME
    )
    shutil.copy(args.rerank_data_config_loc, conf_out_loc)
