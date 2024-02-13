import sys, os
import ipdb
from tqdm import tqdm
from typing import Optional
from data_management.splits import DataSplit, Split, FileInfo
from data_management.dataset_file import DatasetFile
from tactic_gen.lm_example import fmt_from_conf, LmFormatter, LmExample


def get_file_info(data_split: DataSplit, repo_name: str) -> tuple[FileInfo, Split]:
    for split in Split:
        for file_info in data_split.get_file_list(split):
            if file_info.file == repo_name:
                return file_info, split
    raise ValueError(f"File {repo_name} not found.")


def observe_single_file(
    data_split: DataSplit, file: str, formatter: LmFormatter
) -> None:
    test_file_info, split = get_file_info(data_split, file)
    dp_obj = test_file_info.get_dp(data_loc)
    examples: list[LmExample] = []
    for i, proof in enumerate(dp_obj.proofs):
        print(f"Starting Proof {i}")
        for j, step in tqdm(enumerate(proof.steps)):
            example = formatter.example_from_step(
                j, proof, dp_obj, test_file_info, split, data_loc, None
            )
            examples.append(example)
    ipdb.set_trace()


def find_issues(data_split: DataSplit, data_loc: str, proof_loc: str):
    file_count = 0
    for split in Split:
        for file_info in data_split.get_file_list(split):
            try:
                dp_obj = file_info.get_dp(data_loc)
            except FileNotFoundError:
                continue
            if 1 < len(dp_obj.proofs) and os.path.exists(
                os.path.join(proof_loc, file_info.dp_name)
            ):
                proof2 = dp_obj.proofs[1]
                example = formatter.example_from_step(
                    0, proof2, dp_obj, file_info, split, data_loc, None
                )
                if example.input.startswith("<F><P>"):
                    ipdb.set_trace()
            file_count += 1
            print("Num files:", file_count)


proof_bank_loc = "/home/kthompson/coq-modeling/proof-goals"

formatter_conf = {
    "alias": "proof-ret",
    "proof_bank_loc": proof_bank_loc,
    "model_name": "codellama/CodeLlama-7b-hf",
    "state_num_tokens": 220,
    "script_num_tokens": 50,
    "statement_num_tokens": 60,
    "ret_proof_state_tokens": 60,
    "ret_proof_script_tokens": 50,
    "n_step_sampler": {
        "alias": "one",
    },
    "direct_num_steps": False,
}

data_split = DataSplit.load("splits/random-split.json")
data_loc = "raw-data/coq-dataset"
# test_file = "repos/ppedrot-vitef/sheaves/sheaf.v"
# test_file = "repos/tildedave-coq-playground/groups.v"
test_file = "repos/Vickyswj-DiracRepr/Dirac/src/com/reComplex.v"
formatter = fmt_from_conf(formatter_conf)

observe_single_file(data_split, test_file, formatter)
# find_issues(data_split, data_loc, proof_bank_loc)
