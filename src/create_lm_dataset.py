
from typing import Type
import sys, os
import argparse

import jsonlines
from tqdm import tqdm

from lm_example import LmExample, BasicLmExample
from split_raw_data import data_shape_expected, SPLITS
from jsonl_utils import shuffle
from dataset_file import DatasetFile

EXAMPLE_FORMATS: dict[str, Type[LmExample]] = {
    "basic": BasicLmExample,
}

def split_file_path(parent_dir: str, split: str, shuffled: bool=True) -> str:
    if shuffled:
        return os.path.join(parent_dir, f"{split}-shuffled.jsonl")
    else:
        return os.path.join(parent_dir, f"{split}-unshuffled.jsonl")

def create_lm_dataset(partitioned_dataset_loc: str, 
                      example_type: Type[LmExample],
                      output_dataset_loc: str) -> None:
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
            project_examples = example_type.json_from_dataset_file(project_obj)
            output_writer.write_all(project_examples)
        output_writer.close()
        shuffled_output_path = split_file_path(output_dataset_loc, split, shuffled=True)
        print(f"Shuffling {split}")
        shuffle(unshuffled_output_path, shuffled_output_path)
        os.remove(unshuffled_output_path)


if __name__ == "__main__":
    format_options = ", ".join(EXAMPLE_FORMATS.keys())
    parser = argparse.ArgumentParser("Create a jsonl dataset from the data collected by the coq lsp.")
    parser.add_argument("partitioned_dataset_loc", help=f"Location of partitioned dataset.")
    parser.add_argument("output_dataset_loc", help=f"Location to save resulting dataset.")
    parser.add_argument("example_format", help=f"Format of LM example. Options: {format_options}")
    args = parser.parse_args(sys.argv[1:])

    if args.example_format not in EXAMPLE_FORMATS:
        print(f"{args.example_format} is not one of {format_options}.", file=sys.stderr)
        exit(1)

    example_format = EXAMPLE_FORMATS[args.example_format]
    create_lm_dataset(args.partitioned_dataset_loc, 
                      example_format, 
                      args.output_dataset_loc)

    

