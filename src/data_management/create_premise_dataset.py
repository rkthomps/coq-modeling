
import sys, os
import shutil
import argparse
from typing import Type, Any

import jsonlines
from tqdm import tqdm
from yaml import load, Loader

from data_management.dataset_file import DatasetFile, data_shape_expected
from premise_selection.premise_formatter import (
    PREMISE_ALIASES, CONTEXT_ALIASES, ContextFormat, PremiseFormat)
from premise_selection.premise_example import PremiseTrainingExample
from premise_selection.premise_filter import PremiseFilter
from data_management.split_raw_data import SPLITS, split_file_path
from data_management.jsonl_utils import shuffle


PREMISE_CONFIG_NAME = "config.yaml"
def get_examples_from_project(project_obj: DatasetFile,
                              num_negatives_per_positive: int,
                              num_in_file_negatives_per_positive: int,
                              context_format: Type[ContextFormat],
                              premise_format: Type[PremiseFormat],
                              premise_filter: PremiseFilter,
                              ) -> list[Any]:
    training_examples: list[Any] = []
    for proof in project_obj.proofs:
        for step in proof.steps:
            step_examples = PremiseTrainingExample.from_focused_step(
                step, proof, project_obj, num_negatives_per_positive,
                num_in_file_negatives_per_positive, context_format,
                premise_format, premise_filter
            )
            json_examples = [e.to_json() for e in step_examples]
            training_examples.extend(json_examples)
    return training_examples


def create_premise_dataset(partitioned_dataset_loc: str,
                           output_dataset_loc: str,
                           num_negatives_per_positive: int,
                           num_in_file_negatives_per_positive: int,
                           context_format: Type[ContextFormat],
                           premise_format: Type[PremiseFormat],
                           premise_filter: PremiseFilter,
                           ) -> None: 
    if os.path.exists(output_dataset_loc):
        print(f"Dataset already exists at {output_dataset_loc}", file=sys.stderr)
        exit(1)
    os.makedirs(output_dataset_loc)
    for split in SPLITS:
        split_loc = os.path.join(partitioned_dataset_loc, split)
        unshuffled_output_path = split_file_path(output_dataset_loc, split, shuffled=False) 
        output_writer = jsonlines.open(unshuffled_output_path, "a")
        if not os.path.exists(split_loc):
            print(f"{split_loc} does not exist.", file=sys.stderr)
            exit(1)
        assert data_shape_expected(split_loc)
        print(f"Processing {split}...")
        for project in tqdm(os.listdir(split_loc)):
            project_loc = os.path.join(split_loc, project)
            project_obj = DatasetFile.from_directory(project_loc)
            training_json_examples = get_examples_from_project(
                project_obj, num_negatives_per_positive, 
                num_in_file_negatives_per_positive, context_format,
                premise_format, premise_filter)
            output_writer.write_all(training_json_examples)
        output_writer.close()
        shuffled_output_path = split_file_path(output_dataset_loc, split, shuffled=True)
        print(f"Shuffling {split}")
        shuffle(unshuffled_output_path, shuffled_output_path)
        os.remove(unshuffled_output_path)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description=("Create a jsonl dataset from the data "
                     "collected by the coq lsp."))
    parser.add_argument("yaml_config", 
                        help=("Configuration file for creating the premise "
                              "selection dataset."))
    args = parser.parse_args(sys.argv[1:])
    with open(args.yaml_config, "r") as fin:
        conf = load(fin, Loader=Loader)
    partitioned_data_loc = conf["partitioned_data_loc"]
    output_dataset_loc = conf["output_dataset_loc"]
    num_negatives_per_positive = conf["num_negatives_per_positive"]
    num_in_file_negatives_per_positive = conf["num_in_file_negatives_per_positive"]
    context_format_alias = conf["context_format_alias"]
    context_format_type = CONTEXT_ALIASES[context_format_alias]
    premise_format_alias = conf["premise_format_alias"]
    premise_format_type = PREMISE_ALIASES[premise_format_alias]
    premise_filter = PremiseFilter.from_json(conf["premise_filter"])

    create_premise_dataset(
        partitioned_data_loc,
        output_dataset_loc, 
        num_negatives_per_positive,
        num_in_file_negatives_per_positive,
        context_format_type,
        premise_format_type,
        premise_filter,
    )

    config_destination = os.path.join(output_dataset_loc, PREMISE_CONFIG_NAME)
    shutil.copy(args.yaml_config, config_destination)



    


