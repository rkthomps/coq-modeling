import argparse
from pathlib import Path
from data_management.splits import DataSplit, get_all_files


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--dir", required=True, help="Directory to monitor")
    parser.add_argument(
        "--data_splits",
        required=True,
        nargs="+",
        help="Paths to data splits that should be included",
    )

    args = parser.parse_args()
    dir = Path(args.dir)
    splits = [DataSplit.load(Path(s)) for s in args.data_splits]

    all_file_infos = get_all_files(splits)
    for f_info in all_file_infos:
        if not (dir / f_info.dp_name).exists():
            print(f"Missing {f_info.dp_name}")
