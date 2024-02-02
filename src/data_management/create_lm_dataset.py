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

from tactic_gen.lm_example import LmExample, LmFormatter, fmt_from_conf, move_fmt_to
from data_management.splits import (
    FileInfo,
    Split,
    split_file_path,
)
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


@typechecked
class LmExampleConfig:
    FORMATTER_KEY = "lm_formatter"

    def __init__(
        self,
        train_sample: ExampleSample,
        val_sample: ExampleSample,
        test_sample: ExampleSample,
        output_dataset_loc: str,
        lm_formatter: LmFormatter,
    ) -> None:
        self.train_sample = train_sample
        self.val_sample = val_sample
        self.test_sample = test_sample
        self.output_dataset_loc = output_dataset_loc
        self.lm_formatter = lm_formatter

    @classmethod
    def from_config(cls, config: Any) -> LmExampleConfig:
        train_sample_loc = config["train_sample_loc"]
        train_sample = load_sample(train_sample_loc)
        val_sample_loc = config["val_sample_loc"]
        val_sample = load_sample(val_sample_loc)
        test_sample_loc = config["test_sample_loc"]
        test_sample = load_sample(test_sample_loc)
        output_dataset_loc = config["output_dataset_loc"]
        lm_formatter = fmt_from_conf(config["lm_formatter"])
        return cls(
            train_sample, val_sample, test_sample, output_dataset_loc, lm_formatter
        )

    @classmethod
    def load(cls, path: str) -> LmExampleConfig:
        with open(path, "r") as fin:
            yaml_conf = yaml.load(fin, Loader=yaml.Loader)
        return cls.from_config(yaml_conf)


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
    example_sample: ExampleSample,
    lm_formatter: LmFormatter,
    file_info: FileInfo,
    selected_steps: SelectedSteps,
    device_idx: int,
    q: Queue[Optional[LmExample]],
) -> None:
    cuda_str = f"cuda:{device_idx}"
    move_fmt_to(lm_formatter, cuda_str)
    dp_obj = file_info.get_dp(example_sample.data_loc)
    match selected_steps:
        case AllSteps():
            for proof in dp_obj.proofs:
                ground_truth_steps = [s.step.text for s in proof.steps]
                for i in range(len(proof.steps)):
                    example = lm_formatter.example_from_step(
                        i,
                        proof,
                        dp_obj,
                        file_info,
                        example_sample.split,
                        example_sample.data_loc,
                        ground_truth_steps,
                    )
                    q.put(example)
        case CertainSteps(steps=step_idxs):
            for step_idx in step_idxs:
                proof = dp_obj.proofs[step_idx.proof_idx]
                ground_truth_steps = [s.step.text for s in proof.steps]
                example = lm_formatter.example_from_step(
                    step_idx.step_idx,
                    proof,
                    dp_obj,
                    file_info,
                    example_sample.split,
                    example_sample.data_loc,
                    ground_truth_steps,
                )
                q.put(example)


__ArgTuple = tuple[
    ExampleSample, LmFormatter, FileInfo, SelectedSteps, int, Queue[Optional[LmExample]]
]


def __get_split_transformation_args(
    example_sampler: ExampleSample,
    formatter: LmFormatter,
    q: Queue[LmExample | None],
) -> list[__ArgTuple]:
    num_devices = torch.cuda.device_count()
    arg_list: list[__ArgTuple] = []
    for i, (file, selected_steps) in enumerate(example_sampler.step_generator()):
        device_idx = i % num_devices
        arg_list.append(
            (example_sampler, formatter, file, selected_steps, device_idx, q)
        )
    return arg_list


def get_split_transformation_args(
    example_config: LmExampleConfig,
    split: Split,
    q: Queue[Optional[LmExample]],
) -> list[__ArgTuple]:
    match split:
        case Split.TRAIN:
            return __get_split_transformation_args(
                example_config.train_sample, example_config.lm_formatter, q
            )
        case Split.VAL:
            return __get_split_transformation_args(
                example_config.val_sample, example_config.lm_formatter, q
            )
        case Split.TEST:
            return __get_split_transformation_args(
                example_config.test_sample, example_config.lm_formatter, q
            )


if __name__ == "__main__":
    mp.set_start_method("spawn")
    parser = argparse.ArgumentParser(
        "Create a jsonl dataset from the data collected by the coq lsp."
    )
    parser.add_argument(
        "lm_data_config_loc",
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

    example_config = LmExampleConfig.load(args.lm_data_config_loc)

    if os.path.exists(example_config.output_dataset_loc):
        raise FileExistsError(f"{example_config.output_dataset_loc}")
    os.makedirs(example_config.output_dataset_loc)

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
