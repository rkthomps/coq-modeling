from typing import Any, Optional

import jsonlines
import pytorch_lightning as pl
from pytorch_lightning.utilities.types import TRAIN_DATALOADERS
from transformers import AutoTokenizer, GPT2Tokenizer 
from torch.utils.data import Dataset, DataLoader
import torch

from typeguard import typechecked

from data_management.splits import (
    Split,
    split_file_path,
)
from premise_selection.premise_example import PremiseTrainingExample
from premise_selection.training_types import PremiseBatch


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


@typechecked
class PremiseSelectionDataset(Dataset):
    def __init__(
        self,
        premise_file_path: str,
        tokenizer: GPT2Tokenizer,
        max_seq_len: int,
        max_num_examples: Optional[int] = None,
    ) -> None:
        super(PremiseSelectionDataset, self).__init__()
        self.tokenizer = tokenizer
        self.max_seq_len = max_seq_len
        self.examples: list[PremiseTrainingExample] = []

        with jsonlines.open(premise_file_path) as fin:
            for i, obj in enumerate(fin):
                if max_num_examples and i >= max_num_examples:
                    break
                print(f"\rLoading example: {i}", end="")
                self.examples.append(PremiseTrainingExample.from_json(obj))

    def __len__(self) -> int:
        return len(self.examples)

    def __getitem__(self, index: int) -> PremiseTrainingExample:
        return self.examples[index]

    def collate(self, examples: list[PremiseTrainingExample]) -> Any:
        batch_size = len(examples)
        assert len(examples) > 0
        num_positives = 1
        num_negatives = len(examples[0].neg_premises)
        total_num_prems = batch_size * (num_positives + num_negatives)
        label = torch.zeros((batch_size, total_num_prems), dtype=torch.float32)
        for i, example in enumerate(examples):
            for j in range(total_num_prems):
                cur_prem_example = examples[j % batch_size]
                if j < batch_size:
                    cur_prem = cur_prem_example.pos_premise
                else:
                    neg_prem_index = j // batch_size - 1
                    cur_prem = cur_prem_example.neg_premises[neg_prem_index]
                label[i, j] = float(cur_prem in example.all_pos_premises)

        all_batch_premises: list[
            str
        ] = []  # order of adding to this list VERY IMPORTANT
        all_batch_premises.extend([e.pos_premise for e in examples])
        for i in range(num_negatives):
            ith_negative_premises = [e.neg_premises[i] for e in examples]
            all_batch_premises.extend(ith_negative_premises)

        context_list = [e.context for e in examples]

        tokenized_contexts = tokenize_strings(
            self.tokenizer, context_list, self.max_seq_len
        )

        tokenized_prems = tokenize_strings(
            self.tokenizer, all_batch_premises, self.max_seq_len
        )

        context_ids = tokenized_contexts.input_ids
        context_mask = tokenized_contexts.attention_mask
        prem_ids = tokenized_prems.input_ids
        prem_mask = tokenized_prems.attention_mask
        label = label
        return {
            "context_ids": context_ids,
            "context_mask": context_mask,
            "premise_ids": prem_ids,
            "premise_mask": prem_mask,
            "label": label,
        }

        return PremiseBatch(context_ids, context_mask, prem_ids, prem_mask, label)
