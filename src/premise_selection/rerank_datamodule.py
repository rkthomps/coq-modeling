from typing import Any, Optional

import re
import json
import random
import jsonlines
from transformers import AutoTokenizer, GPT2Tokenizer
from torch.utils.data import Dataset, DataLoader
import torch
from pathlib import Path


from data_management.jsonl_utils import ExampleDB
from premise_selection.rerank_example import RerankExample


def tokenize_strings(
    tokenizer: GPT2Tokenizer, strings: list[str], max_seq_len: int
) -> Any:
    return tokenizer(
        strings,
        padding="longest",
        max_length=max_seq_len,
        truncation=True,
        return_tensors="pt",
    )


def allocate_tokens(
    tokenizer: GPT2Tokenizer, s: str, allowance: int, truncate_front: bool = True
) -> tuple[str, int]:
    tokens = tokenizer.encode(s)
    if truncate_front:
        to_add = tokens[(-1 * allowance) :]
    else:
        to_add = tokens[:allowance]
    return tokenizer.decode(to_add, skip_special_tokens=True), len(to_add)


# def mask_premise(premise: str) -> str:
#     premise_name = re.search(r"\S+\s+(\S+?)[\[\]\{\}\(\):=,\s]", premise)
#     if premise_name is None:
#         print("No match for ", premise)
#         return premise
#     match_start, match_end = premise_name.span(1)
#     masked_premise = premise[:match_start] + " <name> " + premise[match_end:]
#     # print(masked_premise)
#     return masked_premise


def collate_examples(
    examples: list[RerankExample],
    tokenizer: GPT2Tokenizer,
    max_seq_len: int,
) -> Any:
    input_strs: list[str] = []
    input_labels: list[int] = []
    sep_str = "\n[SEP]\n"
    num_added_tokens = len(tokenizer.tokenize(sep_str))
    for example in examples:
        premise_str, _ = allocate_tokens(
            tokenizer,
            example.premise,
            (max_seq_len - num_added_tokens) // 2,
            truncate_front=False,
        )
        context_str, _ = allocate_tokens(
            tokenizer,
            example.context,
            (max_seq_len - num_added_tokens) // 2,
            truncate_front=True,
        )
        input_strs.append(f"{premise_str}\n[SEP]\n{context_str}")
        input_labels.append(1 if example.label else 0)

    tokenized_inputs = tokenize_strings(tokenizer, input_strs, max_seq_len)
    return {
        "input_ids": tokenized_inputs.input_ids,
        "mask": tokenized_inputs.attention_mask,
        "labels": torch.tensor(input_labels, dtype=torch.float32),
    }


class RerankDataset(Dataset):
    def __init__(
        self,
        data_path: Path,
        tokenizer: GPT2Tokenizer,
        max_seq_len: int,
        max_n_examples: Optional[int] = None,
    ) -> None:
        super(RerankDataset, self).__init__()
        self.edb = ExampleDB.load(data_path)
        __shuffled_list = list(range(self.edb.size()))
        random.seed(0)
        random.shuffle(__shuffled_list)
        self.edb_map = dict(zip(range(self.edb.size()), __shuffled_list))
        self.tokenizer = tokenizer
        self.max_seq_len = max_seq_len
        self.max_n_examples = max_n_examples

    def __len__(self) -> int:
        if self.max_n_examples is not None:
            return self.max_n_examples
        return self.edb.size()

    def __getitem__(self, idx: int) -> RerankExample:
        target_idx = self.edb_map[idx]
        target_example = RerankExample.from_json(
            json.loads(self.edb.retrieve(target_idx + 1))
        )
        return target_example

    def collate(self, examples: list[RerankExample]) -> Any:
        return collate_examples(examples, self.tokenizer, self.max_seq_len)

    def estimate_pos_freq(self) -> float:
        return 0.5
