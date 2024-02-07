import os
import ipdb
import shutil

from model_deployment.mine_goals import get_file_goals, GoalTermRecord

from coqpyt.coq.base_file import CoqFile

from data_management.splits import DataSplit, Split, FileInfo

SPLIT_LOC = os.path.join("splits", "random-split.json")

DATA_PREFIX = "/home/ubuntu/coq-modeling/raw-data/coq-dataset"

TEST_FILE = "/home/ubuntu/coq-modeling/test-coq-projs/min_superlist.v"

TMP_LOC = "tmp.v"


def get_file_info(data_split: DataSplit, file: str) -> tuple[FileInfo, Split]:
    for split in Split:
        file_list = data_split.get_file_list(split)
        same_name_file = [f for f in file_list if f.file == file]
        if len(same_name_file) > 0:
            return same_name_file[0], split
    raise ValueError(f"{file} not found in split")


data_split = DataSplit.load("splits/random-split.json")
try:
    file_loc = os.path.join(DATA_PREFIX, TEST_FILE)
    file_info, split = get_file_info(data_split, TEST_FILE)
    workspace_loc = os.path.join(DATA_PREFIX, file_info.workspace)
except ValueError:
    file_loc = os.path.abspath(TEST_FILE)
    workspace_loc = os.path.dirname(file_loc)

shutil.copy(file_loc, TMP_LOC)

goal_gen = get_file_goals(file_loc, workspace_loc)
records: list[GoalTermRecord] = []
for g in goal_gen:
    if g:
        records.append(g)
ipdb.set_trace()
