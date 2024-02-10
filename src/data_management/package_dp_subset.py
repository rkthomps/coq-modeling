import sys
import os
import shutil
import argparse

from data_management.splits import DataSplit, Split, str2split, DATA_POINTS_NAME


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "data_split_loc",
    )
    parser.add_argument("split")
    parser.add_argument("data_loc")
    parser.add_argument("out_loc")

    args = parser.parse_args(sys.argv[1:])

    split = str2split(args.split)
    data_split = DataSplit.load(args.data_split_loc)

    for file in data_split.get_file_list(split):
        dp_loc = os.path.join(args.data_loc, DATA_POINTS_NAME, file.dp_name)
        if not os.path.exists(dp_loc):
            print(f"could not find {dp_loc}")
            continue
        shutil.copytree(dp_loc, os.path.join(args.out_loc, file.dp_name))
