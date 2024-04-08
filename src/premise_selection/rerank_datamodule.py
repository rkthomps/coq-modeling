from typing import Any, Optional

import jsonlines
from transformers import AutoTokenizer, GPT2TokenizerFast
from torch.utils.data import Dataset, DataLoader
import torch

from typeguard import typechecked

from data_management.splits import (
    Split,
    split_file_path,
)
from premise_selection.rerank_example import RerankExample


def tokenize_strings(
    tokenizer: GPT2TokenizerFast, strings: list[str], max_seq_len: int
) -> Any:
    return tokenizer(
        strings,
        padding="longest",
        max_length=max_seq_len,
        truncation=True,
        return_tensors="pt",
    )


def allocate_tokens(
    tokenizer: GPT2TokenizerFast, s: str, allowance: int, truncate_front: bool = True
) -> tuple[str, int]:
    tokens = tokenizer.tokenize(s)
    if truncate_front:
        to_add = tokens[(-1 * allowance) :]
    else:
        to_add = tokens[:allowance]
    return tokenizer.convert_tokens_to_string(to_add), len(to_add)


def collate_examples(
    examples: list[RerankExample],
    tokenizer: GPT2TokenizerFast,
    max_seq_len: int,
) -> Any:
    input_strs: list[str] = []
    input_labels: list[int] = []
    for example in examples:
        premise_str, _ = allocate_tokens(
            tokenizer,
            example.premise,
            max_seq_len // 2,
            truncate_front=False,
        )
        context_str, _ = allocate_tokens(
            tokenizer,
            example.context,
            max_seq_len // 2,
            truncate_front=True,
        )
        input_strs.append(f"{premise_str}<SEP>{context_str}")
        input_labels.append(1 if example.label else 0)

    tokenized_inputs = tokenize_strings(tokenizer, input_strs, max_seq_len)
    return {
        "input_ids": tokenized_inputs.input_ids,
        "mask": tokenized_inputs.attention_mask,
        "labels": torch.tensor(input_labels, dtype=torch.float32),
    }


@typechecked
class RerankDataset(Dataset):
    def __init__(
        self,
        rerank_file_path: str,
        tokenizer: GPT2TokenizerFast,
        max_seq_len: int,
        max_num_examples: Optional[int] = None,
    ) -> None:
        super(RerankDataset, self).__init__()
        self.tokenizer = tokenizer
        self.max_seq_len = max_seq_len
        self.examples: list[RerankExample] = []

        with jsonlines.open(rerank_file_path) as fin:
            for i, obj in enumerate(fin):
                if max_num_examples and i >= max_num_examples:
                    break
                if i % 10000 == 0:
                    print(f"\rLoading example: {i}", end="")
                self.examples.append(RerankExample.from_json(obj))

    def __len__(self) -> int:
        return len(self.examples)

    def __getitem__(self, index: int) -> RerankExample:
        return self.examples[index]

    def collate(self, examples: list[RerankExample]) -> Any:
        return collate_examples(examples, self.tokenizer, self.max_seq_len)

    def estimate_pos_freq(self, sample_size: int = 10000) -> float:
        num_pos = 0
        count = 0
        for example in self.examples[:sample_size]:
            if example.label:
                num_pos += 1
            count += 1
        return num_pos / count
