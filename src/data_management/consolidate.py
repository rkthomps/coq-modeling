import sys, os
import argparse
import random
import shutil
import yaml
from pathlib import Path
from tqdm import tqdm

from data_management.jsonl_utils import ExampleDB
from data_management.splits import Split, DataSplit, split2str
from data_management.dataset_utils import DatasetConf, data_conf_from_yaml

from util.util import get_basic_logger

_logger = get_basic_logger(__name__)


def consolidate(
    data_split_loc: Path, input_dataset_loc: Path, output_loc: Path
) -> None:
    tmp_output_loc = Path("/tmp") / str(os.getpid()) / output_loc.name
    if tmp_output_loc.exists():
        shutil.rmtree(tmp_output_loc)
    os.makedirs(tmp_output_loc, exist_ok=True)
    shutil.copy(input_dataset_loc / "conf.yaml", tmp_output_loc)
    data_split = DataSplit.load(data_split_loc)
    for split in Split:
        _logger.info(f"Consolidating {split}")
        split_db = ExampleDB.create(tmp_output_loc / f"{split2str(split)}.db")
        seen_strs: set[int] = set()
        split_num_duplicates = 0
        for file in tqdm(data_split.get_file_list(split)):
            input_file_loc = input_dataset_loc / file.dp_name
            if not input_file_loc.exists():
                _logger.warning(
                    f"Couldn't find file {input_file_loc} during consolidation."
                )
                continue
            batch: list[tuple[str,]] = []
            with input_file_loc.open("r") as fin:
                for line in fin:
                    stripped_line = line.strip()
                    line_hash = hash(stripped_line)
                    if line_hash in seen_strs:
                        split_num_duplicates += 1
                        continue
                    seen_strs.add(line_hash)
                    batch.append((stripped_line,))
            split_db.insert_examples(batch)
        split_db.close()
        _logger.info(
            f"Number of duplicates for {split2str(split)}: {split_num_duplicates}"
        )
    _logger.info("Moving consolidated dataset to final location.")
    shutil.move(tmp_output_loc, output_loc)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        "Takes a distributed set of dataset files; shuffles it; deduplicates it; and writes it to database files."
    )
    parser.add_argument("data_split_loc", help="Location of the data split.")
    parser.add_argument("dataset_loc", help="Location of the dataset.")
    parser.add_argument("output_loc", help="Location of the output.")
    args = parser.parse_args(sys.argv[1:])

    data_split_loc = Path(args.data_split_loc)
    dataset_loc = Path(args.dataset_loc)
    assert dataset_loc.exists()
    dataset_conf_loc = dataset_loc / "conf.yaml"
    assert dataset_conf_loc.exists()

    output_loc = Path(args.output_loc)
    if output_loc.exists():
        raise FileExistsError(f"{output_loc}")

    consolidate(data_split_loc, dataset_loc, output_loc)
