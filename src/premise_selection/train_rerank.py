import argparse
import sys, os
import ipdb
import shutil
from typing import Any, Optional

from data_management.splits import split_file_path, Split
from premise_selection.rerank_datamodule import RerankDataset
from premise_selection.rerank_model import PremiseRerankerConfig, PremiseReranker
from util.constants import PREMISE_DATA_CONF_NAME

from util.train_utils import (
    get_optional_arg,
    load_config,
    get_required_arg,
    get_training_args,
    make_output_dir,
    copy_configs,
)

import transformers
from transformers import TrainingArguments, Trainer, GPT2Tokenizer
from torch.utils.data import Dataset, DataLoader
import torch
import torch.nn.functional as F


def get_tokenizer(conf: dict[str, Any]) -> GPT2Tokenizer:
    model_name = get_required_arg("model_name", conf)
    tokenizer = GPT2Tokenizer.from_pretrained(model_name)
    return tokenizer


def get_model(conf: dict[str, Any]) -> PremiseReranker:
    if "checkpoint_name" in conf:
        model = PremiseReranker.from_pretrained(conf["checkpoint_name"])
        return model

    model_config = PremiseRerankerConfig()
    model = PremiseReranker(model_config)

    return model


def get_datasets(
    conf: dict[str, Any],
    tokenizer: GPT2Tokenizer,
    max_seq_len: int,
) -> tuple[RerankDataset, RerankDataset]:
    data_path = get_required_arg("data_path", conf)
    # num_eval_examples = get_optional_arg("num_eval_examples", conf, None)
    train_path = split_file_path(data_path, Split.TRAIN)
    train_dataset = RerankDataset(
        train_path,
        tokenizer,
        max_seq_len,
    )
    val_path = split_file_path(data_path, Split.VAL)
    val_dataset = RerankDataset(
        val_path, tokenizer, max_seq_len, max_num_examples=10000
    )
    return train_dataset, val_dataset


class BCETrainer(Trainer):

    def __init__(self, pos_freq: float, **kwargs: Any) -> None:
        super(BCETrainer, self).__init__(**kwargs)
        assert 0 < pos_freq
        self.pos_freq = pos_freq
        print("Pos freq:", self.pos_freq)

    def compute_loss(self, model, inputs, return_outputs=False):
        cuda_label = inputs["labels"].to(model.device)
        outputs = model(**inputs)
        logits = outputs["logits"]
        pos_weight = (1 - self.pos_freq) / self.pos_freq
        pos_weight_tensor = torch.tensor(pos_weight, device=model.device)
        loss = F.binary_cross_entropy_with_logits(
            logits, cuda_label, pos_weight=pos_weight_tensor
        )
        # loss = F.binary_cross_entropy(outputs["probs"], cuda_label)
        if return_outputs:
            return loss, outputs
        return loss


def get_trainer(
    conf: dict[str, Any], local_rank: Optional[int], checkpoint_name: Optional[str]
) -> Trainer:
    max_seq_len = get_required_arg("max_seq_len", conf)

    print("\n\nBuilding Training Config...")
    training_args = get_training_args(conf, local_rank)
    print("\n\nRetrieving Tokenizer...")
    tokenizer = get_tokenizer(conf)

    print("\n\nRetrieving Model...")
    model = get_model(conf)

    print("\n\nConstructing Dataset...")
    train_dataset, val_dataset = get_datasets(conf, tokenizer, max_seq_len)

    print("\n\nBuilding Trainer...")
    return BCETrainer(
        pos_freq=train_dataset.estimate_pos_freq(),
        model=model,
        args=training_args,
        train_dataset=train_dataset,
        eval_dataset=val_dataset,
        data_collator=train_dataset.collate,
        tokenizer=tokenizer,
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Train premise selection model by providing a .yaml config file. As an example, see src/tactic_gen/confs/basic_train.yaml"
    )
    print(f"<ARGV>{sys.argv}</ARGV")
    parser.add_argument(
        "--local_rank",
        type=int,
        default=-1,
        help="local rank passed from distributed launcher",
    )
    parser.add_argument("yaml_config", help="yaml config file to use for training.")
    args = parser.parse_args(sys.argv[1:])
    conf = load_config(args.yaml_config)
    train_from_checkpoint = (
        conf["checkpoint_name"] if "checkpoint_name" in conf else None
    )
    trainer = get_trainer(conf, args.local_rank, train_from_checkpoint)
    if train_from_checkpoint:
        checkpoint_name = conf["checkpoint_name"]
        print(f"Training from checkpoint {checkpoint_name}")
        transformers.logging.set_verbosity_info()
        trainer.train(checkpoint_name)
    else:
        make_output_dir(conf)
        copy_configs(args.yaml_config, conf)
        print("Training from scratch")
        trainer.train()
