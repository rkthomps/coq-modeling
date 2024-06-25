from typing import Any, Optional

import random
import json
import jsonlines
from transformers import AutoTokenizer, PreTrainedTokenizer
from torch.utils.data import Dataset, DataLoader
import torch
from pathlib import Path

from data_management.jsonl_utils import ExampleDB
from premise_selection.premise_example import PremiseTrainingExample
from premise_selection.training_types import PremiseBatch


def tokenize_strings(
    tokenizer: PreTrainedTokenizer, strings: list[str], max_seq_len: int
) -> Any:
    return tokenizer(
        strings,
        padding="longest",
        max_length=max_seq_len,
        truncation=True,
        return_tensors="pt",
    )


class PremiseSelectionDataset(Dataset):
    def __init__(
        self,
        data_path: Path,
        tokenizer: PreTrainedTokenizer,
        max_seq_len: int,
        max_n_examples: Optional[int] = None,
    ) -> None:
        super(PremiseSelectionDataset, self).__init__()
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

    def __getitem__(self, idx: int) -> PremiseTrainingExample:
        target_idx = self.edb_map[idx]
        target_example = PremiseTrainingExample.from_json(
            json.loads(self.edb.retrieve(target_idx + 1))
        )
        return target_example

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

        all_batch_premises: list[str] = (
            []
        )  # order of adding to this list VERY IMPORTANT
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
