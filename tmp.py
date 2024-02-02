import os
import shutil
from data_management.splits import DataSplit, FileInfo, Split

data_split = DataSplit.load("splits/random-split.json")
data_loc = "raw-data/coq-dataset"
out_loc = "eval_examples"

for file_info in data_split.get_file_list(Split.VAL):
    file_loc = os.path.join(data_loc, file_info.file)
    dest = os.path.join(out_loc, file_info.dp_name)
    if not os.path.exists(file_loc):
        continue
    shutil.copy(file_loc, dest)
