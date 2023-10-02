from __future__ import annotations
from typing import Type, Optional, Any
import sys, os
import shutil
import argparse

import jsonlines
from tqdm import tqdm
from yaml import load, Loader

from tactic_gen.lm_example import LmExample, BasicLmExample, LMEXAMPLE_ALIASES
from data_management.split_raw_data import SPLITS, split_file_path
from data_management.jsonl_utils import shuffle
from data_management.dataset_file import DatasetFile, data_shape_expected
from model_deployment.premise_model_wrapper import LocalPremiseModelWrapper


def create_lm_dataset(example_config: LmExampleConfig) -> None:
    if os.path.exists(example_config.output_dataset_loc):
        print(f"Dataset already exists at {example_config.output_dataset_loc}", file=sys.stderr)
        exit(1)
    os.makedirs(example_config.output_dataset_loc)
    for split in SPLITS:
        split_loc = os.path.join(example_config.partitioned_dataset_loc, split)
        unshuffled_output_path = split_file_path(example_config.output_dataset_loc, split, shuffled=False) 
        output_writer = jsonlines.open(unshuffled_output_path, "a")
        if not os.path.exists(split_loc):
            print(f"{split_loc} does not exist.", file=sys.stderr)
            exit(1)
        assert data_shape_expected(split_loc)
        print(f"Processing {split}...")
        for project in tqdm(os.listdir(split_loc)):
            project_loc = os.path.join(split_loc, project)
            project_obj = DatasetFile.from_directory(project_loc)
            project_examples = example_config.format_type.json_from_dataset_file(
                project_obj, example_config.premise_wrapper)
            output_writer.write_all(project_examples)
        output_writer.close()
        shuffled_output_path = split_file_path(example_config.output_dataset_loc, split, shuffled=True)
        print(f"Shuffling {split}")
        shuffle(unshuffled_output_path, shuffled_output_path)
        os.remove(unshuffled_output_path)


class LmExampleConfig:
    def __init__(self, partitioned_dataset_loc: str,
                 output_dataset_loc: str,
                 format_type: Type[LmExample],
                 premise_wrapper: Optional[LocalPremiseModelWrapper]) -> None:
        assert type(partitioned_dataset_loc) == str
        assert type(output_dataset_loc) == str
        assert type(format_type) == type
        if premise_wrapper is not None:
            assert isinstance(premise_wrapper, LocalPremiseModelWrapper)
        self.partitioned_dataset_loc = partitioned_dataset_loc
        self.output_dataset_loc = output_dataset_loc
        self.format_type = format_type
        self.premise_wrapper = premise_wrapper

    @classmethod
    def from_json(cls, json_data: Any) -> LmExampleConfig:
        partitioned_dataset_loc = json_data["partitioned_dataset_loc"]
        output_dataset_loc = json_data["output_dataset_loc"]
        format_type_alias = json_data["format_alias"]
        format_type = LMEXAMPLE_ALIASES[format_type_alias]
        if "premise_wrapper_checkpoint" in json_data:
            premise_wrapper_checkpoint = json_data["premise_wrapper_checkpoint"]
            premise_wrapper = LocalPremiseModelWrapper.from_checkpoint(premise_wrapper_checkpoint)
        else:
            premise_wrapper = None
        return cls(partitioned_dataset_loc, output_dataset_loc, format_type, premise_wrapper)

    @classmethod
    def load(cls, path: str) -> LmExampleConfig:
        with open(path, "r") as fin:
            yaml_conf = load(fin, Loader=Loader)
        return cls.from_json(yaml_conf)

    @classmethod
    def void_config(cls) -> LmExampleConfig:
        return cls("", "", LmExample, None)


LM_CONFIG_NAME = "lm-example-conf.yaml"

if __name__ == "__main__":
    parser = argparse.ArgumentParser("Create a jsonl dataset from the data collected by the coq lsp.")
    parser.add_argument("lm_data_config_loc", help="Location of configuration file for LmExample dataset.")
    args = parser.parse_args(sys.argv[1:])

    example_config = LmExampleConfig.load(args.lm_data_config_loc)
    create_lm_dataset(example_config)
    conf_out_loc = os.path.join(example_config.output_dataset_loc, LM_CONFIG_NAME)
    shutil.copy(args.lm_data_config_loc, conf_out_loc)

