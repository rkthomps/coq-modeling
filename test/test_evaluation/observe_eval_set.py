import os

import ipdb

import datetime
from evaluation.eval_set import DataSplitEvalSet
from data_management.splits import Split


random_split_loc = os.path.join("splits", "random-split.json")
data_loc = os.path.join("raw-data", "coq-dataset")
curtime = datetime.datetime.now()
eval_tmp_loc = os.path.join(
    "evals",
    "tmp",
    f"{curtime.year}-{curtime.month}-{curtime.day}-{curtime.hour}-{curtime.minute}-{curtime.second}",
)

conf = {
    "data_split_loc": random_split_loc,
    "split": "val",
    "data_loc": data_loc,
    "eval_tmp_loc": eval_tmp_loc,
    "seed": 0,
}

eval_set = DataSplitEvalSet.from_conf(conf)
for proof in eval_set.get_proof_gen():
    ipdb.set_trace()
