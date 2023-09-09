

from typing import Any 

import sys, os

import pytorch_lightning as pl
from pytorch_lightning.utilities.types import EVAL_DATALOADERS, TRAIN_DATALOADERS
import torch
from torch.utils.data import Dataset, DataLoader
import jsonlines
from transformers import AutoTokenizer, ByT5Tokenizer

from lm_example import LmExample
from create_lm_dataset import split_file_path
from split_raw_data import TRAIN_NAME, VAL_NAME, TEST_NAME


Batch =  dict[str, Any]
class CoqLmDataset(Dataset):
    def __init__(self, dataset_file: str, 
                 tokenizer: ByT5Tokenizer,
                 max_seq_len: int) -> None:
        super().__init__()
        self.dataset_file = dataset_file
        assert os.path.exists(self.dataset_file)
        assert self.dataset_file.endswith("shuffled.jsonl")
        self.tokenizer = tokenizer 
        self.max_seq_len = max_seq_len
        self.data: list[LmExample] = []
        with jsonlines.open(self.dataset_file) as fin:
            for obj in fin:
                example = LmExample.from_json(obj) 
                self.data.append(example)

    def __getitem__(self, index: int) -> LmExample:
        return self.data[index]

    def __len__(self) -> int:
        return len(self.data)

    def collate(self, examples: list[LmExample]) -> Batch:
        inputs = [e.input for e in examples]
        tokenized_inputs = self.tokenizer(inputs, 
                                          padding="longest",
                                          max_length=self.max_seq_len,
                                          truncation=True,
                                          return_tensors="pt")
        outputs = [e.output for e in examples]
        tokenized_outputs = self.tokenizer(inputs, 
                                           padding="longest",
                                           max_length=self.max_seq_len,
                                           truncation=True,
                                           return_tensors="pt")
        batch = {
            "inputs": inputs,
            "input_ids": tokenized_inputs.input_ids,
            "input_mask": tokenized_inputs.attention_mask,
            "outputs": outputs,
            "output_ids": tokenized_outputs.input_ids,
            "output_mask": tokenized_outputs.attention_mask,
        }
        return batch


class GeneratorDataModule(pl.LightningDataModule):
    def __init__(self, data_path: str, 
                 model_name: str,
                 batch_size: int, 
                 eval_batch_size: int,
                 max_seq_len: int) -> None:
        super().__init__()
        self.data_path = data_path
        self.model_name = model_name
        self.batch_size = batch_size
        self.eval_batch_size = eval_batch_size
        self.max_seq_len = max_seq_len
        self.tokenizer = AutoTokenizer.from_pretrained(model_name)

    def setup(self, stage: str) -> None:
        if stage in (None, "fit"):
            train_data_path = split_file_path(self.data_path, TRAIN_NAME)
            self.ds_train = CoqLmDataset(train_data_path, 
                                         self.tokenizer,
                                         self.max_seq_len)
        if stage in (None, "fit", "validate"):
            val_data_path = split_file_path(self.data_path, VAL_NAME)
            self.ds_val = CoqLmDataset(val_data_path, 
                                       self.tokenizer,
                                       self.max_seq_len)

    def train_dataloader(self) -> TRAIN_DATALOADERS:
        return DataLoader(
            self.ds_train, 
            self.batch_size,
            collate_fn=self.ds_train.collate,
            pin_memory=True,
            drop_last=True,
        ) 

    def val_dataloader(self) -> EVAL_DATALOADERS:
        return DataLoader(
            self.ds_val, 
            self.batch_size,
            collate_fn=self.ds_val.collate,
            pin_memory=True,
            drop_last=True,
        ) 

    def test_dataloader(self) -> EVAL_DATALOADERS:
        raise NotImplementedError

    def predict_dataloader(self) -> EVAL_DATALOADERS:
        raise NotImplementedError

    def teardown(self, stage: str) -> None:
        raise NotImplementedError





    
