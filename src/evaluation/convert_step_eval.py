import os
import sys
import argparse
import shutil
import time

from tqdm import tqdm

from data_management.dataset_file import DatasetFile
from data_management.splits import DataSplit, Split, FileInfo
from evaluation.step_eval import ATTEMPTS_NAME, FileEval, FileEvalOld

from util.util import get_basic_logger

_logger = get_basic_logger(__name__)


bank: dict[FileInfo, DatasetFile] = {}


def get_dp(
    data_loc: str, dp_name: str, data_split: DataSplit, split: Split
) -> DatasetFile:
    for file_info in data_split.get_file_list(split):
        if file_info.dp_name == dp_name:
            if file_info in bank:
                return bank[file_info]
            else:
                dp_obj = file_info.get_dp(data_loc)
                bank[file_info] = dp_obj
                return dp_obj
    raise ValueError(f"Could not find file for {dp_name}")


def convert_eval(
    data_loc: str, data_split: DataSplit, old_dir: str, new_dir: str
) -> None:
    os.makedirs(new_dir)
    old_conf_loc = os.path.join(old_dir, "step-conf.yaml")
    new_conf_loc = os.path.join(new_dir, "step-conf.yaml")
    shutil.copy(old_conf_loc, new_conf_loc)
    old_attempts_loc = os.path.join(old_dir, ATTEMPTS_NAME)
    new_attempts_loc = os.path.join(new_dir, ATTEMPTS_NAME)
    os.makedirs(new_attempts_loc)
    for attempt in tqdm(os.listdir(old_attempts_loc)):
        attempt_loc = os.path.join(old_attempts_loc, attempt)
        new_attempt_loc = os.path.join(new_attempts_loc, attempt)
        dp_obj = get_dp(data_loc, attempt, data_split, Split.VAL)
        old_file_obj = FileEvalOld.load(attempt_loc)
        new_file_obj = old_file_obj.to_file_eval_new(dp_obj)
        new_file_obj.save(new_attempt_loc)


def convert_evals(
    data_loc: str, data_split: DataSplit, old_dir: str, new_dir: str
) -> None:
    os.makedirs(new_dir)
    for eval in os.listdir(old_dir):
        _logger.info(f"Converting {eval}")
        convert_eval(
            data_loc,
            data_split,
            os.path.join(old_dir, eval),
            os.path.join(new_dir, eval),
        )


if __name__ == "__main__":
    parser = argparse.ArgumentParser("Convert step eval to annoted step eval")
    parser.add_argument("data_loc", help="Location of data")
    parser.add_argument("data_split_loc", help="Location of data split")
    parser.add_argument("old_dir", help="Old directory of evals")
    parser.add_argument("new_dir", help="New directory of evals")
    args = parser.parse_args(sys.argv[1:])
    assert os.path.exists(args.old_dir)
    assert not os.path.exists(args.new_dir)

    data_split = DataSplit.load(args.data_split_loc)
    convert_evals(args.data_loc, data_split, args.old_dir, args.new_dir)
