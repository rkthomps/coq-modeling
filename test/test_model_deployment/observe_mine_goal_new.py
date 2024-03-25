import os
import ipdb
import shutil

from model_deployment.mine_goals import get_file_goals, GoalThreadReturn

from coqpyt.coq.base_file import CoqFile

from data_management.splits import DataSplit, Split, FileInfo

SPLIT_LOC = os.path.join("splits", "random-split.json")

DATA_PREFIX = "/home/ubuntu/coq-modeling/raw-data/coq-dataset"

#TEST_FILE = "repos/yj-han-software-foundations/plf/Hoare2.v"
#TEST_FILE = "coq-community-corn-reals-stdlib-CMTMeasurableFunctions.v"
TEST_FILE = "repos/coq-community-corn/ftc/WeakIVTQ.v"

TMP_LOC = "tmp.v"


def get_file_info(data_split: DataSplit, file: str) -> tuple[FileInfo, Split]:
    for split in Split:
        file_list = data_split.get_file_list(split)
        same_name_file = [f for f in file_list if f.file == file]
        if len(same_name_file) > 0:
            return same_name_file[0], split
    raise ValueError(f"{file} not found in split")


data_split = DataSplit.load("splits/final-split.json")

file_info, split = get_file_info(data_split, TEST_FILE)
file_loc = os.path.join(DATA_PREFIX, file_info.file)
workspace_loc = os.path.join(DATA_PREFIX, file_info.workspace)

shutil.copy(file_loc, TMP_LOC)

ret_obj = GoalThreadReturn(None)

goal_gen = get_file_goals(DATA_PREFIX, file_info, ret_obj, 60)
if ret_obj.file_goals:
    ipdb.set_trace()
