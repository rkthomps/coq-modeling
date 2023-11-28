from typing import Any, Optional

import jsonlines
import pytorch_lightning as pl
from pytorch_lightning.utilities.types import TRAIN_DATALOADERS
from transformers import AutoTokenizer, ByT5Tokenizer
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
    tokenizer: ByT5Tokenizer, strings: list[str], max_seq_len: int
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
        premise_data_path: str,
        splits: list[Split],
        tokenizer: ByT5Tokenizer,
        max_seq_len: int,
    ) -> None:
        super(PremiseSelectionDataset, self).__init__()
        self.tokenizer = tokenizer
        self.max_seq_len = max_seq_len
        self.examples: list[PremiseTrainingExample] = []
        for split in splits:
            split_file = split_file_path(premise_data_path, split)
            with jsonlines.open(split_file, "r") as fin:
                for obj in fin:
                    self.examples.append(PremiseTrainingExample.from_json(obj))

    def __len__(self) -> int:
        return len(self.examples)

    def __getitem__(self, index: int) -> PremiseTrainingExample:
        return self.examples[index]

    def collate(self, examples: list[PremiseTrainingExample]) -> PremiseBatch:
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

        return PremiseBatch(context_ids, context_mask, prem_ids, prem_mask, label)


@typechecked
class PremiseDataModule(pl.LightningDataModule):
    def __init__(
        self,
        premise_data_path: str,
        model_name: str,
        max_seq_len: int,
        batch_size: int,
        eval_batch_size: int,
        num_workers: int,
    ) -> None:
        super(PremiseDataModule, self).__init__()
        self.premise_data_path = premise_data_path
        self.model_name = model_name
        self.max_seq_len = max_seq_len
        self.batch_size = batch_size
        self.eval_batch_size = eval_batch_size
        self.num_workers = num_workers

        self.tokenizer = ByT5Tokenizer.from_pretrained(model_name)

    def setup(self, stage: Optional[str]) -> None:
        self.train_ds = PremiseSelectionDataset(
            self.premise_data_path,
            [Split.TRAIN],
            self.tokenizer,
            self.max_seq_len,
        )
        self.val_ds = PremiseSelectionDataset(
            self.premise_data_path,
            [Split.VAL],
            self.tokenizer,
            self.max_seq_len,
        )
        self.predict_ds = PremiseSelectionDataset(
            self.premise_data_path,
            [Split.TRAIN, Split.VAL, Split.TEST],
            self.tokenizer,
            self.max_seq_len,
        )

    def prepare_data(self) -> None:
        """
        Not downloading anything so I don't believe I need
        to worry about corruption
        """
        pass

    def train_dataloader(self) -> TRAIN_DATALOADERS:
        return DataLoader(
            self.train_ds,
            batch_size=self.batch_size,
            num_workers=self.num_workers,
            collate_fn=self.train_ds.collate,
            shuffle=False,
            pin_memory=True,
            drop_last=True,
        )

    def val_dataloader(self) -> TRAIN_DATALOADERS:
        return DataLoader(
            self.val_ds,
            batch_size=self.eval_batch_size,
            num_workers=self.num_workers,
            collate_fn=self.train_ds.collate,
            shuffle=False,
            pin_memory=True,
            drop_last=False,
        )

    def predict_dataloader(self) -> TRAIN_DATALOADERS:
        return DataLoader(
            self.predict_ds,
            batch_size=self.eval_batch_size,
            num_workers=self.num_workers,
            collate_fn=self.train_ds.collate,
            shuffle=False,
            pin_memory=True,
            drop_last=False,
        )
