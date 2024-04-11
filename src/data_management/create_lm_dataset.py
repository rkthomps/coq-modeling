from __future__ import annotations
from typing import Optional, Any
import sys, os
import shutil
import argparse
import pickle
import multiprocessing as mp
from queue import Queue
from dataclasses import dataclass
from pathlib import Path
from util.constants import CLEAN_CONFIG


import json
from tqdm import tqdm
import yaml

from tactic_gen.lm_example import (
    LmExample,
    LmFormatter,
    FormatterConf,
    formatter_from_conf,
    formatter_conf_from_yaml,
)
from data_management.splits import (
    FileInfo,
    Split,
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


@dataclass
class LmDatasetConf:
    n_procs: int
    train_sample_loc: Path
    val_sample_loc: Path
    test_sample_loc: Path
    sentence_db_loc: Path
    output_dataset_loc: Path
    lm_formatter_conf: FormatterConf

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> LmDatasetConf:
        return cls(
            yaml_data["n_procs"],
            Path(yaml_data["train_sample_loc"]),
            Path(yaml_data["val_sample_loc"]),
            Path(yaml_data["test_sample_loc"]),
            Path(yaml_data["sentence_db_loc"]),
            Path(yaml_data["output_dataset_loc"]),
            formatter_conf_from_yaml(yaml_data["lm_formatter"]),
        )


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
    sentence_db_loc: Path,
    selected_steps: SelectedSteps,
    q: Queue[Optional[LmExample]],
) -> None:
    sentence_db = SentenceDB.load(sentence_db_loc)
    dp_obj = file_info.get_dp(example_sample.data_loc, sentence_db)
    match selected_steps:
        case AllSteps():
            for proof in dp_obj.proofs:
                ground_truth_steps = [s.step.text for s in proof.steps]
                for i in range(len(proof.steps)):
                    example = lm_formatter.example_from_step(
                        i,
                        proof,
                        dp_obj=dp_obj,
                        file_info=file_info,
                        split=example_sample.split,
                        data_loc=example_sample.data_loc,
                        ground_truth_steps=ground_truth_steps,
                        key_record=None,
                        cutoff_idx=None,
                    )
                    q.put(example)
        case CertainSteps(steps=step_idxs):
            for step_idx in step_idxs:
                proof = dp_obj.proofs[step_idx.proof_idx]
                ground_truth_steps = [s.step.text for s in proof.steps]
                example = lm_formatter.example_from_step(
                    step_idx.step_idx,
                    proof,
                    dp_obj=dp_obj,
                    file_info=file_info,
                    split=example_sample.split,
                    data_loc=example_sample.data_loc,
                    ground_truth_steps=ground_truth_steps,
                    key_record=None,
                    cutoff_idx=None,
                )
                q.put(example)


__ArgTuple = tuple[
    ExampleSample,
    LmFormatter,
    FileInfo,
    Path,
    SelectedSteps,
    Queue[Optional[LmExample]],
]


def __get_split_transformation_args(
    example_sampler: ExampleSample,
    formatter: LmFormatter,
    sentence_db_loc: Path,
    q: Queue[LmExample | None],
) -> list[__ArgTuple]:
    arg_list: list[__ArgTuple] = []
    for file, selected_steps in example_sampler.step_generator():
        arg_list.append(
            (
                example_sampler,
                formatter,
                file,
                sentence_db_loc,
                selected_steps,
                q,
            )
        )
    return arg_list


def get_split_transformation_args(
    data_config: LmDatasetConf,
    split: Split,
    q: Queue[Optional[LmExample]],
) -> list[__ArgTuple]:
    match split:
        case Split.TRAIN:
            sample = load_sample(data_config.train_sample_loc)
        case Split.VAL:
            sample = load_sample(data_config.val_sample_loc)
        case Split.TEST:
            sample = load_sample(data_config.test_sample_loc)

    lm_formatter = formatter_from_conf(data_config.lm_formatter_conf)
    return __get_split_transformation_args(
        sample,
        lm_formatter,
        data_config.sentence_db_loc,
        q,
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        "Create a jsonl dataset from the data collected by the coq lsp."
    )
    parser.add_argument(
        "lm_data_config_loc",
        help="Location of configuration file for LmExample dataset.",
    )

    conf_path = Path(f"./{CLEAN_CONFIG}")
    assert conf_path.exists()
    with conf_path.open("rb") as fin:
        example_conf: LmDatasetConf = pickle.load(fin)

    args = parser.parse_args(sys.argv[1:])
    if example_conf.n_procs < 2:
        raise ValueError("Data processing needs at least 2 processes.")

    with open(args.lm_data_config_loc, "r") as fin:
        yaml_data = yaml.load(fin, Loader=yaml.Loader)
        data_conf = LmDatasetConf.from_yaml(yaml_data)

    if os.path.exists(data_conf.output_dataset_loc):
        raise FileExistsError(f"{data_conf.output_dataset_loc}")
    os.makedirs(data_conf.output_dataset_loc)

    with mp.Manager() as manager:
        q: Queue[Optional[LmExample]] = manager.Queue()
        with mp.Pool(example_conf.n_procs) as pool:
            for split in [Split.TEST, Split.VAL, Split.TRAIN]:
                split_args = get_split_transformation_args(data_conf, split, q)
                raw_path = split_file_path(
                    data_conf.output_dataset_loc,
                    split,
                    shuffled=False,
                    deduplicated=False,
                )
                deduped_path = split_file_path(
                    data_conf.output_dataset_loc,
                    split,
                    shuffled=False,
                    deduplicated=True,
                )
                shuffled_path = split_file_path(
                    data_conf.output_dataset_loc,
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

    conf_out_loc = os.path.join(data_conf.output_dataset_loc, DATA_CONF_NAME)
    shutil.copy(args.lm_data_config_loc, conf_out_loc)
