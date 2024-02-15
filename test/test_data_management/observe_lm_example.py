import sys, os
import ipdb
from tqdm import tqdm
from typing import Optional
from data_management.splits import DataSplit, Split, FileInfo, file_from_split
from data_management.dataset_file import DatasetFile
from tactic_gen.lm_example import fmt_from_conf, LmFormatter, LmExample


def all_files(data_split: DataSplit, formatter: LmFormatter):
    dp_obj: Optional[DatasetFile] = None
    f_info: Optional[FileInfo] = None
    success_file: Optional[int] = None
    for i, file_info in enumerate(data_split.get_file_list(Split.TRAIN)):
        f_info = file_info
        success_file = i
        if not os.path.exists(os.path.join(proof_bank_loc, f_info.dp_name)):
            continue
        try:
            dp_obj = file_info.get_dp("raw-data/coq-dataset")
        except FileNotFoundError:
            continue
        if 1 < len(dp_obj.proofs):
            break
    print(f"Success after {success_file} files")
    assert dp_obj is not None
    assert f_info is not None

    formatter = fmt_from_conf(formatter_conf)
    example = formatter.example_from_step(
        0, dp_obj.proofs[1], dp_obj, f_info, Split.TRAIN, data_loc, None
    )
    print(example.input)
    print(example.output)


def one_file(
    file: str, data_split: DataSplit, data_loc: str, formatter: LmFormatter
) -> None:
    file_info, split = file_from_split(file, data_split)
    file_dp = file_info.get_dp(data_loc)
    examples: list[LmExample] = []
    for proof in file_dp.proofs:
        for i, step in enumerate(proof.steps):
            example = formatter.example_from_step(
                i, proof, file_dp, file_info, split, data_loc, None
            )
            examples.append(example)
    return examples

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

one_file_name = "repos/snu-sf-paco/src/paco13.v"

formatter = fmt_from_conf(formatter_conf)

one_file(one_file_name, data_split, data_loc, formatter)
