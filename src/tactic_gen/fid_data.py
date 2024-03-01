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

from transformers import T5Tokenizer, BatchEncoding
from tactic_gen.lm_example import LmExample


class FidDataset(torch.utils.data.Dataset):
    def __init__(
        self,
        data_path: str,
        tokenizer: T5Tokenizer,
        max_encode_len: int,
        max_decode_len: int,
        max_num_passages: int,
        max_n_examples: Optional[int] = None,
    ):
        self.max_encode_len = max_encode_len
        self.max_decode_len = max_decode_len
        self.max_num_passages = max_num_passages
        self.max_n_examples = max_n_examples
        self.tokenizer = tokenizer

        self.raw_examples: list[LmExample] = []
        with jsonlines.open(data_path) as fin:
            for i, obj in enumerate(fin):
                print(f"\rLoading example: {i}", end="")
                self.raw_examples.append(LmExample.from_json(obj))
                if max_n_examples and len(self.raw_examples) >= max_n_examples:
                    break

    def __len__(self) -> int:
        return len(self.raw_examples)

    def __getitem__(self, idx: int) -> LmExample:
        return self.raw_examples[idx]

    def __fmt_target(self, s: str) -> str:
        return s + " </s>"

    def get_example_inputs(self, example: LmExample) -> list[str]:
        if (
            example.passages is None
            or len(example.passages) == 0
            or self.max_num_passages <= 0
        ):
            return [example.input]
        return [
            f"{example.input} {p}" for p in example.passages[: self.max_num_passages]
        ]

    def collate(self, examples: list[LmExample]) -> Any:
        targets = [self.__fmt_target(e.output) for e in examples]
        target_batch = self.tokenizer.batch_encode_plus(
            targets,
            max_length=self.max_decode_len,
            pad_to_max_length=True,
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
                pad_to_max_length=True,
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
        }
