
import argparse
import sys, os
import random
import shutil
from tqdm import tqdm

from dataset_file import STEPS_NAME, FILE_CONTEXT_NAME

TRAIN_NAME = "train"
VAL_NAME = "val"
TEST_NAME = "test"

SPLITS = [TRAIN_NAME, VAL_NAME, TEST_NAME]


def data_shape_expected(raw_data_loc: str) -> bool:
    for project in os.listdir(raw_data_loc):
        project_loc = os.path.join(raw_data_loc, project)
        if not os.path.isdir(project_loc):
            print(f"{project_loc} is not a directory.", file=sys.stderr)
            exit(1)
        project_files = set(os.listdir(project_loc))
        if not project_files == set([STEPS_NAME, FILE_CONTEXT_NAME]):
            print(f"{project_loc} does not exclusively contain files {STEPS_NAME} and {FILE_CONTEXT_NAME}")
            exit(1)
    return True


def split_dataset(raw_data_loc: str, 
                  train_prop: float, 
                  val_prop: float, 
                  test_prop: float) -> None:
    assert data_shape_expected(raw_data_loc)
    new_base_dir = f"{raw_data_loc}-split"

    train_split = os.path.join(new_base_dir, TRAIN_NAME)
    val_split = os.path.join(new_base_dir, VAL_NAME)
    test_split = os.path.join(new_base_dir, TEST_NAME)

    destinations = [train_split, val_split, test_split]
    weights = [train_prop, val_prop, test_prop]
    print("Partitioning Coq Files into train/val/test...")
    for project in tqdm(os.listdir(raw_data_loc)):
        project_cur_dir = os.path.join(raw_data_loc, project)
        project_parent_dir_selection = random.choices(destinations, weights)
        assert len(project_parent_dir_selection) == 1
        project_parent_dir = project_parent_dir_selection[0]
        project_new_dir = os.path.join(project_parent_dir, project) 
        shutil.copytree(project_cur_dir, project_new_dir)

    assert data_shape_expected(train_split)
    assert data_shape_expected(val_split)
    assert data_shape_expected(test_split)


if __name__ == "__main__":
    parser = argparse.ArgumentParser("Split a raw dataset into train/val/test by file.")
    parser.add_argument("raw_data_loc", help="Location of raw dataset.")
    parser.add_argument("train_prop", type=float, help="Proportion of the files to use for training.")
    parser.add_argument("val_prop", type=float, help="Proportion of the files to use for validation.")
    parser.add_argument("test_prop", type=float, help="Proportion of the files to use for testing.")
    args = parser.parse_args(sys.argv[1:])

    if (not args.train_prop + args.val_prop + args.test_prop == 1):
        print(f"{args.train_prop} + {args.val_prop} + {args.test_prop} != 1", file=sys.stderr)
        exit(1)
    
    split_dataset(args.raw_data_loc, args.train_prop, args.val_prop, args.test_prop)

    
