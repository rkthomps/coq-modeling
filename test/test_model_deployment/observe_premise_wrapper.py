from data_management.splits import DataSplit, Split
from model_deployment.premise_model_wrapper import (
    premise_wrapper_from_conf,
    get_ranked_premise_generator,
    move_prem_wrapper_to,
)


conf = {
    "alias": "local",
    "checkpoint_loc": "models/prem-select-no-coq-crossent/checkpoint-7278",
}

pw = premise_wrapper_from_conf(conf)
move_prem_wrapper_to(pw, "cuda")

data_split = DataSplit.load("splits/random-split.json")
data_loc = "raw-data/coq-dataset"

for file_info in data_split.get_file_list(Split.TRAIN):
    try:
        file_dp = file_info.get_dp(data_loc)
    except FileNotFoundError:
        continue
    for proof in file_dp.proofs:
        for step in proof.steps:
            pos_avail_premises = pw.premise_filter.get_pos_and_avail_premises(
                step, proof, file_dp
            )
            gen = get_ranked_premise_generator(
                pw, step, proof, pos_avail_premises.avail_premises
            )
            for obj in gen:
                print(obj.text)
