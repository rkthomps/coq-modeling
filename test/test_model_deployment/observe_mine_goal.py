import os
import shutil

from model_deployment.mine_goal_terms import mine_coq_file_goals

from coqpyt.coq.base_file import CoqFile

from data_management.splits import DataSplit, Split, FileInfo

SPLIT_LOC = os.path.join("splits", "random-split.json")

DATA_PREFIX = "/home/ubuntu/coq-modeling/raw-data/coq-dataset"

TEST_FILE = "repos/jonsterling-coq-algebra-experiments/theories/Foundation.v"

TMP_LOC = "tmp.v"


def get_file_info(data_split: DataSplit, file: str) -> tuple[FileInfo, Split]:
    for split in Split:
        file_list = data_split.get_file_list(split)
        same_name_file = [f for f in file_list if f.file == file]
        if len(same_name_file) > 0:
            return same_name_file[0], split
    raise ValueError(f"{file} not found in split")


data_split = DataSplit.load("splits/random-split.json")
file_loc = os.path.join(DATA_PREFIX, TEST_FILE)
file_info, split = get_file_info(data_split, TEST_FILE)
workspace_loc = os.path.join(DATA_PREFIX, file_info.workspace)
shutil.copy(file_loc, TMP_LOC)

with CoqFile(os.path.abspath(TMP_LOC), workspace=workspace_loc) as coq_file:
    print(coq_file.is_valid)
    mine_coq_file_goals(coq_file, file_info, split)