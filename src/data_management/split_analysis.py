import sys, os
import argparse

from data_management.splits import DataSplit, Split, Project


def largest_projects(data_split: DataSplit, split: Split, n: int) -> list[Project]:
    projects = data_split.get_project_list(split)
    sorted_projects = sorted(projects, key=lambda p: -1 * len(p.files))
    greater_than_n = [p for p in sorted_projects if len(p.files) > n]
    return greater_than_n


def pretty_print_projects(projects: list[Project], split: Split, data_loc: str) -> None:
    print(f"{len(projects)} largest projects in {split.name}:")
    for project in projects:
        project_time = project.get_creation_time(data_loc)
        print(
            "\t{:30s} has {:4d} files, {:4d} stars, and was created {:s}.".format(
                project.repo_name,
                len(project.files),
                project.get_num_stars(),
                project_time.strftime("%Y/%m/%d"),
            )
        )
    print()


def analyze_split(data_split: DataSplit, data_loc: str, n: int = 10) -> None:
    for split in Split:
        big_projects = largest_projects(data_split, split, n)
        pretty_print_projects(big_projects, split, data_loc)


if __name__ == "__main__":
    parser = argparse.ArgumentParser("Find large projects and times.")
    parser.add_argument("data_split_loc", help="Location of data split.")
    parser.add_argument(
        "data_loc", help="Location of raw data with repos subdirectory."
    )
    args = parser.parse_args(sys.argv[1:])
    ds = DataSplit.load(args.data_split_loc)
    analyze_split(ds, args.data_loc)
