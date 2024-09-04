from typing import Optional, Iterable, Generator, Any
import sys, os
import shutil
import re
import time
import argparse
import functools
import subprocess
from pathlib import Path

from yaml import load, Loader
import jsonlines

from peft import LoraConfig, get_peft_model, prepare_model_for_kbit_training
import transformers
from transformers import (
    AutoModelForCausalLM,
    AutoTokenizer,
    PreTrainedModel,
    PreTrainedTokenizer,
    BitsAndBytesConfig,
    TrainingArguments,
    CodeLlamaTokenizer,
    Trainer,
)
import torch
from torch.utils.data import Dataset
from trl import SFTTrainer, DataCollatorForCompletionOnlyLM

# from datasets import Dataset
import numpy as np

from util.train_utils import (
    get_optional_arg,
    get_required_arg,
    get_training_args,
    load_config,
    make_output_dir,
    copy_configs,
    get_train_val_path,
    TrainType,
    TRAINING_CONF_NAME,
    REQS_NAME,
    GIT_NAME,
)
from util.util import set_rango_logger
from util.constants import RANGO_LOGGER
from data_management.splits import Split
from lemma_gen.lemma_data import (
    LemmaDataset,
    ExampleCollatorConf,
    example_collator_from_conf,
    example_collator_conf_from_yaml,
    get_tokenizer,
)

import logging

_logger = logging.getLogger(RANGO_LOGGER)


# This doc details how to finetune codellama:
# https://github.com/huggingface/trl/blob/main/examples/scripts/sft_trainer.py

# More ideas for arguments here:
# https://huggingface.co/docs/transformers/main_classes/trainer#transformers.TrainingArguments


def get_lora_conf(conf: dict[str, Any]) -> LoraConfig:
    peft_config = LoraConfig(
        lora_alpha=16,
        lora_dropout=0.1,
        r=64,
        bias="none",
        task_type="CAUSAL_LM",
        target_modules="all-linear",
    )
    return peft_config


def get_model(model_name: str) -> PreTrainedModel:
    bnb_config = BitsAndBytesConfig(
        load_in_4bit=True,
        bnb_4bit_quant_type="nf4",
        bnb_4bit_compute_dtype=torch.bfloat16,
        bnb_4bit_use_double_quant=True,
        bnb_4bit_quant_storage=torch.bfloat16,
    )

    model = AutoModelForCausalLM.from_pretrained(
        model_name,
        quantization_config=bnb_config,
        torch_dtype=torch.bfloat16,
    )

    # https://huggingface.co/docs/bitsandbytes/main/en/fsdp_qlora
    # model = prepare_model_for_kbit_training(model)
    # https://github.com/microsoft/DeepSpeed/blob/master/deepspeed/inference/quantization/quantization.py
    # https://github.com/microsoft/DeepSpeedExamples/tree/master/inference/huggingface/zero_inference
    return model


def get_datasets(
    conf: dict[str, Any],
) -> tuple[LemmaDataset, LemmaDataset]:
    example_collator_yaml_conf = get_required_arg("example_collator", conf)
    data_path = Path(get_required_arg("data_path", conf))
    num_eval_examples = get_optional_arg("num_eval_examples", conf, None)
    hard_seq_len = get_required_arg("hard_seq_len", conf)
    train_path, val_path = get_train_val_path(data_path)

    example_collator_conf = example_collator_conf_from_yaml(example_collator_yaml_conf)
    example_collator = example_collator_from_conf(example_collator_conf)
    print("EXAMPLE COLLATOR", example_collator)
    tokenizer = get_tokenizer(get_required_arg("model_name", conf))
    train_dataset = LemmaDataset(train_path, tokenizer, example_collator, hard_seq_len)
    val_dataset = LemmaDataset(
        val_path,
        tokenizer,
        example_collator,
        hard_seq_len,
        num_eval_examples,
    )
    return train_dataset, val_dataset


# def formatting_func(examples: list[str]) -> list[str]:
#     # Formatting is done upon dataset creation
#     return examples


def get_trainer(
    conf: dict[str, Any], local_rank: Optional[int], checkpoint_name: Optional[str]
) -> Trainer:
    print("\n\nBuilding Training Config...")
    training_args = get_training_args(conf, local_rank)

    print("\n\nRetrieving Model...")
    model_name = get_required_arg("model_name", conf)
    raw_model = get_model(model_name)
    lora_config = get_lora_conf(conf)
    model = get_peft_model(raw_model, lora_config)

    print("\n\nConstructing Dataset...")
    train_dataset, val_dataset = get_datasets(conf)

    print(train_dataset.tokenizer.decode(train_dataset[0].input_ids))

    print("\n\nBuilding Trainer...")
    # trainer = SFTTrainer(
    #     model=model,
    #     tokenizer=tokenizer,
    #     args=training_args,
    #     data_collator=train_dataset.collator,
    #     train_dataset=train_dataset,
    #     eval_dataset=val_dataset,
    #     max_seq_length=hard_seq_len,
    # )

    trainer = Trainer(
        model=model,
        tokenizer=train_dataset.tokenizer,
        args=training_args,
        data_collator=train_dataset.collator,
        train_dataset=train_dataset,
        eval_dataset=val_dataset,
        # max_seq_length=hard_seq_len,
    )
    return trainer


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Train code llama by providing a .yaml config file. As an example, see src/tactic_gen/confs/basic_train.yaml"
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
    set_rango_logger(__file__, logging.DEBUG)
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
        copy_configs(args.yaml_config, conf, TrainType.LEMMA)
        print("Training from scratch")
        trainer.train()
