# Copyright (c) Facebook, Inc. and its affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

from typing import Optional, Any
import torch
import random
import json
import jsonlines
import numpy as np
from pathlib import Path

from data_management.jsonl_utils import ExampleDB
from transformers import AutoTokenizer, BatchEncoding
from tactic_gen.lm_example import LmExample


class FidDataset(torch.utils.data.Dataset):
    def __init__(
        self,
        data_path: Optional[Path],
        tokenizer: AutoTokenizer,
        max_encode_len: int,
        max_decode_len: int,
        max_num_passages: int,
        max_num_examples: Optional[int] = None,
    ):
        self.max_encode_len = max_encode_len
        self.max_decode_len = max_decode_len
        self.max_num_passages = max_num_passages
        self.tokenizer = tokenizer
        self.max_num_examples = max_num_examples

        if data_path is not None:
            self.example_db = ExampleDB.load(data_path)
        else:
            self.example_db = None

    def __len__(self) -> int:
        assert self.example_db is not None
        if self.max_num_examples is not None:
            return self.max_num_examples
        return self.example_db.size()

    def __getitem__(self, idx: int) -> LmExample:
        assert self.example_db is not None
        return LmExample.from_json(json.loads(self.example_db.retrieve(idx + 1)))

    def get_example_inputs(self, example: LmExample) -> list[str]:
        if (
            example.passages is None
            or len(example.passages) == 0
            or self.max_num_passages == 0
        ):
            passage_inputs = [f"{example.input}"]
        else:
            passage_inputs = [
                f"{example.input} {p}"
                for p in example.passages[: self.max_num_passages]
            ]
        padding = ["" for _ in range(self.max_num_passages - len(passage_inputs))]
        return passage_inputs + padding

    def collate(self, examples: list[LmExample]) -> Any:
        targets = [e.output for e in examples]
        target_batch = self.tokenizer.batch_encode_plus(
            targets,
            max_length=self.max_decode_len,
            padding="max_length",
            return_tensors="pt",
            truncation=True,
        )

        target_ids = target_batch["input_ids"]
        target_mask = target_batch["attention_mask"].bool()
        target_ids = target_ids.masked_fill(~target_mask, -100)

        batch_input_ids: list[torch.Tensor] = []
        batch_attention_masks: list[torch.Tensor] = []
        for example in examples:
            inputs = self.get_example_inputs(example)
            encoded_inputs = self.tokenizer.batch_encode_plus(
                inputs,
                max_length=self.max_encode_len,
                padding="max_length",
                return_tensors="pt",
                truncation=True,
            )
            batch_input_ids.append(encoded_inputs["input_ids"][None])
            batch_attention_masks.append(encoded_inputs["attention_mask"][None])

        input_ids = torch.cat(batch_input_ids, dim=0)
        input_masks = torch.cat(batch_attention_masks, dim=0)
        return {
            "input_ids": input_ids,
            "attention_mask": input_masks.bool(),
            "labels": target_ids,
            # "return_dict": False,  # Or else get error for encoder_outputs being a tuple
        }
