from __future__ import annotations
from typing import Type, Optional, Any
import sys, os
import shutil
import argparse
import multiprocessing as mp

from typeguard import typechecked
import json
from tqdm import tqdm
from yaml import load, Loader

from tactic_gen.n_step_sampler import NStepSampler
from tactic_gen.lm_example import LmExample, BasicLmExample, LMEXAMPLE_ALIASES
from data_management.splits import DataSplit, Split, split_file_path, DATA_POINTS_NAME
from data_management.jsonl_utils import shuffle, deduplicate
from data_management.dataset_file import DatasetFile
from model_deployment.premise_model_wrapper import LocalPremiseModelWrapper


@typechecked
class LmExampleConfig:
    def __init__(
        self,
        data_split: DataSplit,
        data_loc: str,
        output_dataset_loc: str,
        format_type: Type[LmExample],
        premise_wrapper: Optional[LocalPremiseModelWrapper],
        n_step_sampler: Optional[NStepSampler],
    ) -> None:
        self.data_split = data_split
        self.data_loc = data_loc
        self.output_dataset_loc = output_dataset_loc
        self.format_type = format_type
        self.premise_wrapper = premise_wrapper
        self.n_step_sampler = n_step_sampler

    def to_json(self) -> Any:
        json_data: Any = {
            "data_split": self.data_split.to_json(),
            "data_loc": self.data_loc,
            "output_dataset_loc": self.output_dataset_loc,
            "format_alias": self.format_type.get_alias(),
        }
        if self.premise_wrapper:
            json_data[
                "premise_wrapper_checkpoint"
            ] = self.premise_wrapper.checkpoint_loc
        if self.n_step_sampler:
            json_data["n_step_sampler"] = self.n_step_sampler.to_json()
        return json_data

    @classmethod
    def from_json(cls, json_data: Any) -> LmExampleConfig:
        data_split = DataSplit.load(json_data["data_split"])
        data_loc = json_data["data_loc"]
        output_dataset_loc = json_data["output_dataset_loc"]
        format_type_alias = json_data["format_alias"]
        format_type = LMEXAMPLE_ALIASES[format_type_alias]

        if "premise_wrapper_checkpoint" in json_data:
            premise_wrapper_checkpoint = json_data["premise_wrapper_checkpoint"]
            premise_wrapper = LocalPremiseModelWrapper.from_checkpoint(
                premise_wrapper_checkpoint
            )
        else:
            premise_wrapper = None

        if "n_step_sampler" in json_data:
            n_step_sampler = NStepSampler.from_json(json_data["n_step_sampler"])
        else:
            n_step_sampler = None
        return cls(
            data_split,
            data_loc,
            output_dataset_loc,
            format_type,
            premise_wrapper,
            n_step_sampler,
        )

    @classmethod
    def load(cls, path: str) -> LmExampleConfig:
        with open(path, "r") as fin:
            yaml_conf = load(fin, Loader=Loader)
        return cls.from_json(yaml_conf)

    @classmethod
    def void_config(cls) -> LmExampleConfig:
        # ADD DATA SPLIT
        data_loc = ""
        data_split = DataSplit.void_split()
        output_dataset_loc = ""
        format_type = LmExample
        premise_wrapper = None
        n_step_sampler = None
        return cls(
            data_split,
            data_loc,
            output_dataset_loc,
            format_type,
            premise_wrapper,
            n_step_sampler,
        )

    @classmethod
    def from_example_type_and_premise_wrapper(
        cls,
        example_type: type[LmExample],
        premise_wrapper: Optional[LocalPremiseModelWrapper],
    ) -> LmExampleConfig:
        data_loc = ""
        data_split = DataSplit.void_split()
        output_dataset_loc = ""
        n_step_sampler = None
        return cls(
            data_split,
            data_loc,
            output_dataset_loc,
            example_type,
            premise_wrapper,
            n_step_sampler,
        )


def writer(q: mp.Queue[Optional[LmExample]], out_file: str) -> None:
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
    example_config: LmExampleConfig, dp_loc: str, q: mp.Queue[Optional[LmExample]]
) -> None:
    dp_obj = DatasetFile.from_directory(dp_loc)
    examples = example_config.format_type.from_dataset_file(
        dp_obj, example_config.premise_wrapper, example_config.n_step_sampler
    )
    for example in examples:
        q.put(example)


def get_split_transformation_args(
    example_config: LmExampleConfig, split: Split, q: mp.Queue[LmExample]
) -> list[tuple[LmExampleConfig, str, mp.Queue[LmExample]]]:
    transformation_args: list[tuple[LmExampleConfig, str, mp.Queue[LmExample]]] = []
    for project in example_config.data_split.get_project_list(split):
        for file in project.files:
            dp_loc = os.path.join(
                example_config.data_loc, DATA_POINTS_NAME, file.dp_name
            )
            transformation_args.append((example_config, dp_loc, q))
    return transformation_args


DATA_CONF_NAME = "lm-example-conf.yaml"

if __name__ == "__main__":
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

    example_config = LmExampleConfig.load(args.lm_data_config_loc)

    if os.path.exists(example_config.output_dataset_loc):
        raise FileExistsError(f"{example_config.output_dataset_loc}")
    os.makedirs(example_config.output_dataset_loc)

    with mp.Manager() as manager:
        q: mp.Queue[Optional[LmExample]] = manager.Queue()
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
