
from typing import Any

import argparse
import sys, os
import random
import shutil
import json
from tqdm import tqdm

from data_management.dataset_file import data_shape_expected

TRAIN_NAME = "train"
VAL_NAME = "val"
TEST_NAME = "test"
ASSIGNMENT_NAME = "assignments.json"

SPLITS = [TRAIN_NAME, VAL_NAME, TEST_NAME]


def split_file_path(parent_dir: str, split: str, shuffled: bool=True) -> str:
    if shuffled:
        return os.path.join(parent_dir, f"{split}-shuffled.jsonl")
    else:
        return os.path.join(parent_dir, f"{split}-unshuffled.jsonl")


def assignment_shape_expected(assignment: Any) -> bool:
    if not type(assignment) == dict:
        print("Supplied assignment is not a dictionary", file=sys.stderr)
        exit(1)
    ass_keys = set(assignment.keys())
    ex_keys = set(SPLITS)
    if not ass_keys == ex_keys:
        print(f"Supplied assignment has unexpected keys. {ass_keys} instead of {ex_keys}")
        exit(1)
    for split in SPLITS:
        if not all([type(p) == str for p in assignment[split]]):
            print(f"Unexpected type in {split} split of assignment. Expected list[str].",
                  file=sys.stderr)
            exit(1)
    return True


def split_dataset_from_assignment(raw_data_loc: str, 
                                  split_assignments: dict[str, list[str]]) -> None:
    """
    Use a previous assignment to split the dataset.
    The previous assignment should be of the form:
    "train": ["coq-file1", "coq-file2", "coq-file3", ...]
    "val": ...
    "test": ...
    """
    assert data_shape_expected(raw_data_loc)
    raw_files = set(os.listdir(raw_data_loc))
    if not (raw_files == (
        set(split_assignments["train"]) | 
        set(split_assignments["val"]) | 
        set(split_assignments["test"]))):
        print(f"Cannot use existing assignment to split the raw files. There is a mismatch between the set of coq files in the assignment and the set of coq files in the data.",
              file=sys.stderr)
        exit(1)
    new_base_dir = f"{raw_data_loc}-split"
    if os.path.exists(new_base_dir):
        print(f"It looks like you already have partitioned this data into {new_base_dir}. Consider partitioning into a different directory.")
        exit(1)
    for split_name, coq_files in split_assignments.items():
        new_split_dir = os.path.join(new_base_dir, split_name)
        print(f"Copying {split_name}...")
        os.makedirs(new_split_dir)
        for coq_file in tqdm(coq_files):
            old_loc = os.path.join(raw_data_loc, coq_file)
            new_loc = os.path.join(new_split_dir, coq_file)
            shutil.copytree(old_loc, new_loc)
        assert data_shape_expected(new_split_dir)
    with open(os.path.join(new_base_dir, ASSIGNMENT_NAME), "w") as fout:
        fout.write(json.dumps(split_assignments, indent=2))


def split_dataset(raw_data_loc: str, 
                  train_prop: float, 
                  val_prop: float, 
                  test_prop: float) -> None:
    assert data_shape_expected(raw_data_loc)
    new_base_dir = f"{raw_data_loc}-split"
    if os.path.exists(new_base_dir):
        print(f"It looks like you already have partitioned this data into {new_base_dir}. Consider partitioning into a different directory.")
        exit(1)

    assignment_loc = os.path.join(new_base_dir, ASSIGNMENT_NAME)

    dest_names = [TRAIN_NAME, VAL_NAME, TEST_NAME]
    weights = [train_prop, val_prop, test_prop]
    assignment: dict[str, list[str]] = {}
    print("Partitioning Coq Files into train/val/test...")
    for project in tqdm(os.listdir(raw_data_loc)):
        project_cur_dir = os.path.join(raw_data_loc, project)
        dest_name_selection = random.choices(dest_names, weights)
        assert len(dest_name_selection) == 1
        dest_name = dest_name_selection[0]
        if dest_name not in assignment:
            assignment[dest_name] = []
        assignment[dest_name].append(project)
        project_new_dir = os.path.join(new_base_dir, dest_name, project)
        shutil.copytree(project_cur_dir, project_new_dir)

    with open(assignment_loc, "w") as fout:
        fout.write(json.dumps(assignment, indent=2))
    assert data_shape_expected(os.path.join(new_base_dir, TRAIN_NAME))
    assert data_shape_expected(os.path.join(new_base_dir, VAL_NAME))
    assert data_shape_expected(os.path.join(new_base_dir, TEST_NAME))


if __name__ == "__main__":
    parser = argparse.ArgumentParser("Split a raw dataset into train/val/test by file. Must provide --train_prop, --val_prop, and --test_prop. Or can provide existing assignment file. ")
    parser.add_argument("raw_data_loc", help="Location of raw dataset.")
    parser.add_argument("--train_prop", type=float, help="Proportion of the files to use for training.")
    parser.add_argument("--val_prop", type=float, help="Proportion of the files to use for validation.")
    parser.add_argument("--test_prop", type=float, help="Proportion of the files to use for testing.")
    parser.add_argument("--assignment", "-a", type=str, help="Path to existing splits. This argument will split weights.")
    args = parser.parse_args(sys.argv[1:])

    if args.assignment:
        with open(args.assignment, "r") as fin:
            assignment = json.load(fin)
        assert assignment_shape_expected(assignment)
        split_dataset_from_assignment(args.raw_data_loc, assignment)
        exit(0)

    if not all([args.train_prop, args.val_prop, args.test_prop]):
        print("You must also provide arguments --train_prop, --val_prop, and --test_prop if you do not provide an assignment.",
                file=sys.stderr)
        exit(1)

    if (not args.train_prop + args.val_prop + args.test_prop == 1):
        print(f"{args.train_prop} + {args.val_prop} + {args.test_prop} != 1", file=sys.stderr)
        exit(1)
    split_dataset(args.raw_data_loc, args.train_prop, args.val_prop, args.test_prop)

    
