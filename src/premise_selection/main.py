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


class DualObjective(Trainer):

    def __init__(self, sim_weight: float, mask_prob: int, **kwargs: Any):
        super(DualObjective, self).__init__(**kwargs)
        self.sim_weight = sim_weight
        self.mask_prob = mask_prob

    def get_similarity_loss(self, label: torch.Tensor, outputs: dict[str, Any]):
        temp = 0.1
        similarities = outputs["similarities"]
        cooled_dots = similarities / temp
        pos_mask = -1e9 * (1 - label)
        pos_weight = torch.logsumexp(cooled_dots + pos_mask, dim=1)
        total_weight = torch.logsumexp(cooled_dots, dim=1)
        diffs = pos_weight - total_weight
        assert (diffs <= 0).all()
        num_posities = label.sum(axis=1)
        pos_avg = diffs / num_posities
        batch_avg = pos_avg.mean()
        loss = -1 * batch_avg
        return loss

    def get_clm_loss(
        self, inputs: torch.Tensor, input_mask: torch.Tensor, logits: torch.Tensor
    ):
        vocab_size = logits.shape[-1]
        shift_logits = logits[..., :-1, :].contiguous()
        shift_labels = inputs[..., 1:].contiguous()
        reshape_logits = shift_logits.view(-1, vocab_size)
        reshape_labels = shift_labels.view(-1)
        # print(inputs.shape)
        # print(logits.shape)
        loss = torch.nn.CrossEntropyLoss()
        return loss(reshape_logits, reshape_labels)

    def get_mlm_loss(
        self, labels: torch.Tensor, input_mask: torch.Tensor, logits: torch.Tensor
    ):
        loss = torch.nn.CrossEntropyLoss()
        vocab_size = logits.shape[-1]
        return loss(logits.view(-1, vocab_size), labels.view(-1))

    def compute_loss(self, model, inputs, return_outputs=False):
        pad_token_id = 1  # for gpt2tokenizer
        premise_mlm_mask = (
            torch.rand(inputs["premise_ids"].shape, device="cuda") < self.mask_prob
        )
        context_mlm_mask = (
            torch.rand(inputs["context_ids"].shape, device="cuda") < self.mask_prob
        )

        premise_mask = inputs["premise_mask"] & ~premise_mlm_mask
        context_mask = inputs["context_mask"] & ~context_mlm_mask

        premise_inputs = torch.where(
            premise_mask == 1, inputs["premise_ids"], pad_token_id
        )
        context_inputs = torch.where(
            context_mask == 1, inputs["context_ids"], pad_token_id
        )

        premise_labels = torch.where(premise_mask == 0, inputs["premise_ids"], -100)
        context_labels = torch.where(context_mask == 0, inputs["context_ids"], -100)

        cuda_label = inputs["label"].to(model.device)
        # TODO HERE
        outputs = model(
            context_ids=context_inputs,
            context_mask=context_mask,
            premise_ids=premise_inputs,
            premise_mask=premise_mask,
            label=cuda_label,
        )

        similarity_loss = self.get_similarity_loss(cuda_label, outputs)
        premise_reconstruction_loss = self.get_mlm_loss(
            premise_labels, premise_mask, outputs["premise_logits"]
        )
        context_reconstruction_loss = self.get_mlm_loss(
            context_labels, context_mask, outputs["context_logits"]
        )
        # print(
        #     "sim",
        #     similarity_loss,
        #     "prem",
        #     premise_reconstruction_loss,
        #     "ctxt",
        #     context_reconstruction_loss,
        # )
        reconstruct_weight = (1 - self.sim_weight) / 2
        loss = (
            self.sim_weight * similarity_loss
            + reconstruct_weight * premise_reconstruction_loss
            + reconstruct_weight * context_reconstruction_loss
        )
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
    elif loss_fn == "dual":
        mask_prob = get_optional_arg("mask_prob", conf, 0.15)
        sim_weight = get_optional_arg("sim_weight", conf, 0.8)
        return DualObjective(
            model=model,
            args=training_args,
            train_dataset=train_dataset,
            eval_dataset=val_dataset,
            data_collator=train_dataset.collate,
            tokenizer=tokenizer,
            mask_prob=mask_prob,
            sim_weight=sim_weight,
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
