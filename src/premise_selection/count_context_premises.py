from typing import Generator

import sys
import os
import json
import argparse
import re

from data_management.splits import split_file_path, Split
from transformers import CodeLlamaTokenizer
from tactic_gen.codellama_data import collate_example
from tactic_gen.train_codellama import get_tokenizer

from tactic_gen.lm_example import PREM_SEP, THM_SEP


def count_premises(
    data_loc: str, input_len: int = 448, seq_len: int = 512
) -> Generator[int, None, None]:
    path = split_file_path(data_loc, Split.TRAIN)
    tokenizer = get_tokenizer(
        {"model_name": "codellama/CodeLlama-7b-hf", "max_seq_len": seq_len}
    )
    with open(path, "r") as fin:
        for i, line in enumerate(fin):
            print(f"\rProcessed {i}", end="")
            obj = json.loads(line.strip())
            input = obj["input"]
            output = obj["output"]
            new_in, _ = collate_example(tokenizer, input_len, seq_len, input, output)
            first_premise = re.search(r"Premise (\d+):", new_in)
            if first_premise:
                (num_premise_str,) = first_premise.groups()
                yield int(num_premise_str)
            else:
                yield 0


def count_chars(
    data_loc: str, input_len: int = 448, seq_len: int = 512
) -> Generator[dict[str, int], None, None]:
    path = split_file_path(data_loc, Split.TRAIN)
    tokenizer = get_tokenizer(
        {"model_name": "codellama/CodeLlama-7b-hf", "max_seq_len": seq_len}
    )
    with open(path, "r") as fin:
        for i, line in enumerate(fin):
            print(f"\rProcessed {i}", end="")
            obj = json.loads(line.strip())
            input = obj["input"]
            output = obj["output"]
            new_in, _ = collate_example(tokenizer, input_len, seq_len, input, output)
            prem_end_idx = new_in.index(PREM_SEP) if PREM_SEP in new_in else None
            proof_end_idx = new_in.index(THM_SEP) if THM_SEP in new_in else None
            if proof_end_idx is None:
                yield {
                    "goal": len(new_in),
                    "proof": 0,
                    "premises": 0,
                }
            elif prem_end_idx is None:
                goal_start_idx = proof_end_idx + len(THM_SEP)
                goal_len = len(new_in) - goal_start_idx
                yield {
                    "goal": goal_len,
                    "proof": goal_start_idx,
                    "premises": 0,
                }
            else:
                proof_start_idx = prem_end_idx + len(PREM_SEP)
                goal_start_idx = proof_end_idx + len(THM_SEP)
                yield {
                    "goal": len(new_in) - goal_start_idx,
                    "proof": proof_end_idx - proof_start_idx,
                    "premises": prem_end_idx,
                }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("data_loc", help="Processed Data Loc")
    args = parser.parse_args(sys.argv[1:])
    count_premises(args.data_loc)
