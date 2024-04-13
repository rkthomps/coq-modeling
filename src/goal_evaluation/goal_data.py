
from typing import Any, Optional

import jsonlines
from transformers import AutoTokenizer, GPT2Tokenizer
from torch.utils.data import Dataset, DataLoader
import torch
from pathlib import Path

from data_management.splits import (
    Split,
    split_file_path,
)
from goal_evaluation.goal_example import GoalExample

SEP_ID = 3
START_ID = 4

def tokenize_example(tokenizer: GPT2Tokenizer, max_seq_len: int, example: GoalExample) -> dict[str, list[int]]:
    assert tokenizer.truncation_side == "left"
    result = tokenizer(example.goal, truncation=True, max_length=max_seq_len - 2)
    return result


def collate_examples(
    examples: list[GoalExample],
    tokenizer: GPT2Tokenizer,
    max_seq_len: int,
) -> Any:
    input_ids: list[list[int]] = []
    attention_masks: list[list[int]] = []
    for example in examples:
        result = tokenize_example(tokenizer, max_seq_len, example)
        goal_ids: list[int] = result["input_ids"]
        goal_attn_mask: list[int] = result["attention_mask"]
        goal_ids += [SEP_ID, min(START_ID + example.n_step_left, len(tokenizer) - 1)]
        goal_attn_mask += [1, 1]
        assert len(goal_ids) <= max_seq_len
        assert len(goal_attn_mask) <= max_seq_len
        assert len(goal_ids) == len(goal_attn_mask)
        input_ids.append(goal_ids)
        attention_masks.append(goal_attn_mask)
    
    max_len = max(len(iids) for iids in input_ids)
    padded_input_ids = [iid + [tokenizer.pad_token_id for _ in range(max_len - len(iid))] for iid in input_ids]
    padded_attention_mask = [m + [0 for _ in range(max_len - len(m))] for m in attention_masks]
    input_tensor = torch.tensor(padded_input_ids)
    mask_tensor = torch.tensor(padded_attention_mask)

    targets = torch.zeros(input_tensor.shape)
    for i in range(len(input_ids)):
        idx = len(input_ids[i]) - 1
        targets[i, idx] = 1

    #labels = torch.where(input_tensor == tokenizer.pad_token_id, -100, input_tensor)
    labels = torch.where(targets == 1, input_tensor, -100)
    assert input_tensor.shape == mask_tensor.shape
    return {
        "input_ids": input_tensor,
        "attention_mask": mask_tensor,
        "labels": labels,
    }


class GoalDataset(Dataset):
    def __init__(
        self,
        goal_file_path: Path,
        tokenizer: GPT2Tokenizer,
        max_seq_len: int,
        max_num_examples: Optional[int] = None,
    ) -> None:
        super(GoalDataset, self).__init__()
        self.tokenizer = tokenizer
        self.max_seq_len = max_seq_len
        self.examples: list[GoalExample] = []

        with jsonlines.open(goal_file_path) as fin:
            for i, obj in enumerate(fin):
                if max_num_examples and i >= max_num_examples:
                    break
                if i % 10000 == 0:
                    print(f"\rLoading example: {i}", end="")
                self.examples.append(GoalExample.from_json(obj))

    def __len__(self) -> int:
        return len(self.examples)

    def __getitem__(self, index: int) -> GoalExample:
        return self.examples[index]

    def collate(self, examples: list[GoalExample]) -> Any:
        return collate_examples(examples, self.tokenizer, self.max_seq_len)
