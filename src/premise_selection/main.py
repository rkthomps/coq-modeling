import argparse
import sys, os
import ipdb
import shutil
from typing import Any, Optional

from data_management.splits import split_file_path, Split
from premise_selection.datamodule import PremiseSelectionDataset
from premise_selection.model import PremiseRetriever, PremiseRetrieverConfig
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


def get_model(conf: dict[str, Any]) -> PremiseRetriever:
    if "checkpoint_name" in conf:
        model = PremiseRetriever.from_pretrained(conf["checkpoint_name"])
        return model

    model_config = PremiseRetrieverConfig()
    model = PremiseRetriever(model_config)

    return model


def get_datasets(
    conf: dict[str, Any],
    tokenizer: GPT2Tokenizer,
    max_seq_len: int,
) -> tuple[PremiseSelectionDataset, PremiseSelectionDataset]:
    data_path = get_required_arg("data_path", conf)
    # num_eval_examples = get_optional_arg("num_eval_examples", conf, None)
    train_path = split_file_path(data_path, Split.TRAIN)
    train_dataset = PremiseSelectionDataset(train_path, tokenizer, max_seq_len)
    val_path = split_file_path(data_path, Split.VAL)
    val_dataset = PremiseSelectionDataset(
        val_path, tokenizer, max_seq_len, max_num_examples=10000
    )
    return train_dataset, val_dataset


class MSETrainer(Trainer):
    def compute_loss(self, model, inputs, return_outputs=False):
        cuda_label = inputs["label"].to(model.device)
        outputs = model(**inputs)
        similarities = outputs["similarities"]
        loss = F.mse_loss(similarities, cuda_label)
        if return_outputs:
            return loss, outputs
        return loss


class CrossEntTrainer(Trainer):
    def compute_loss(self, model, inputs, return_outputs=False):
        temp = 0.1
        cuda_label = inputs["label"].to(model.device)
        outputs = model(**inputs)
        similarities = outputs["similarities"]
        cooled_dots = similarities / temp
        pos_mask = -1e9 * (1 - cuda_label)
        pos_weight = torch.logsumexp(cooled_dots + pos_mask, dim=1)
        total_weight = torch.logsumexp(cooled_dots, dim=1)
        diffs = pos_weight - total_weight
        assert (diffs <= 0).all()
        num_posities = cuda_label.sum(axis=1)
        pos_avg = diffs / num_posities
        batch_avg = pos_avg.mean()
        loss = -1 * batch_avg
        if return_outputs:
            return loss, outputs
        return loss


def get_trainer(
    conf: dict[str, Any], local_rank: Optional[int], checkpoint_name: Optional[str]
) -> Trainer:
    max_seq_len = get_required_arg("max_seq_len", conf)

    print("\n\nBuilding Training Config...")
    training_args = get_training_args(conf, local_rank)
    print("weight decay:", training_args.weight_decay)
    print("\n\nRetrieving Tokenizer...")
    tokenizer = get_tokenizer(conf)

    print("\n\nRetrieving Model...")
    model = get_model(conf)

    print("\n\nConstructing Dataset...")
    train_dataset, val_dataset = get_datasets(conf, tokenizer, max_seq_len)

    print("\n\nBuilding Trainer...")
    loss_fn = get_optional_arg("loss_fn", conf, "mse")
    print(f"\n\nUsing {loss_fn} loss")
    if loss_fn == "cross-entropy":
        return CrossEntTrainer(
            model=model,
            args=training_args,
            train_dataset=train_dataset,
            eval_dataset=val_dataset,
            data_collator=train_dataset.collate,
            tokenizer=tokenizer,
        )
    else:
        return MSETrainer(
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
