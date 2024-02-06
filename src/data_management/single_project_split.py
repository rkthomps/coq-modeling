import sys
import os
import argparse
import random
from data_management.splits import DataSplit, Split, FileInfo, Project


def create_single_project_split(large_split: DataSplit, project: str) -> DataSplit:
    train_files: list[FileInfo] = []
    val_files: list[FileInfo] = []
    train_split = 0.8
    for split in Split:
        files = large_split.get_file_list(split)
        for file in files:
            if file.repository != project:
                continue
            if random.random() < train_split:
                train_files.append(file)
            else:
                val_files.append(file)

    train_projects = [Project(project, train_files)]
    val_projects = [Project(project, val_files)]
    new_split = DataSplit(train_projects, val_projects, [])
    return new_split


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Make a file-wise split for a single project"
    )
    parser.add_argument("complete_split_loc", help="Complete split loc")
    parser.add_argument("project_name", help="project name")
    parser.add_argument("save_loc", help="Where to save new split")
    args = parser.parse_args(sys.argv[1:])

    large_split = DataSplit.load(args.complete_split_loc)
    project_split = create_single_project_split(large_split, args.project_name)
    project_split.save(args.save_loc)
