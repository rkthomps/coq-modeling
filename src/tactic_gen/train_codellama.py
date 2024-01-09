from typing import Optional, Iterable, Generator, Any
import sys, os
import shutil
import re
import time
import argparse
import functools
import subprocess

from yaml import load, Loader
import jsonlines

from peft import LoraConfig, get_peft_model, prepare_model_for_kbit_training
import transformers
from transformers import (
    LlamaForCausalLM,
    CodeLlamaTokenizer,
    BitsAndBytesConfig,
    TrainingArguments,
    Trainer,
    HfArgumentParser,
    BatchEncoding,
)
from transformers.integrations import HfDeepSpeedConfig
from deepspeed.inference.quantization.quantization import (
    _init_group_wise_weight_quantization,
)
import torch
from torch.utils.data import Dataset

# from datasets import Dataset
import numpy as np

from util.train_utils import (
    get_optional_arg,
    get_required_arg,
    get_training_args,
    load_config,
    make_output_dir,
    copy_configs,
    TRAINING_CONF_NAME,
    REQS_NAME,
    GIT_NAME,
)
from tactic_gen.lm_example import LmExample
from tactic_gen.codellama_data import LmDataset
from data_management.splits import Split, split2str, split_file_path
from data_management.create_lm_dataset import DATA_CONF_NAME


# This doc details how to finetune codellama:
# https://github.com/huggingface/trl/blob/main/examples/scripts/sft_trainer.py

# More ideas for arguments here:
# https://huggingface.co/docs/transformers/main_classes/trainer#transformers.TrainingArguments


def get_lora_conf(conf: dict[str, Any]) -> LoraConfig:
    return LoraConfig(
        r=get_required_arg("peft_lora_r", conf),
        lora_alpha=get_required_arg("peft_lora_alpha", conf),
        bias="none",
        task_type="CAUSAL_LM",
    )


def get_model(conf: dict[str, Any]) -> LlamaForCausalLM:
    model_name = get_required_arg("model_name", conf)
    quantization_config = BitsAndBytesConfig(
        load_in_4bit=True,
        llm_int8_enable_fp32_cpu_offload=True,
        bnb_4bit_use_double_quant=True,
        bnb_4bit_quant_type="nf4",
        bnb_4bit_compute_dtype=torch.bfloat16,
    )

    model = LlamaForCausalLM.from_pretrained(
        model_name,
        quantization_config=quantization_config,
        load_in_4bit=True,
        torch_dtype=torch.float16,
    )

    model = prepare_model_for_kbit_training(model)
    # https://github.com/microsoft/DeepSpeed/blob/master/deepspeed/inference/quantization/quantization.py
    # https://github.com/microsoft/DeepSpeedExamples/tree/master/inference/huggingface/zero_inference
    assert type(model) == LlamaForCausalLM
    return model


def get_datasets(
    conf: dict[str, Any],
    tokenizer: CodeLlamaTokenizer,
    max_input_len: int,
    max_seq_len: int,
) -> tuple[LmDataset, LmDataset]:
    data_path = get_required_arg("data_path", conf)
    num_eval_examples = get_optional_arg("num_eval_examples", conf, None)
    train_path = split_file_path(data_path, Split.TRAIN)
    train_dataset = LmDataset(train_path, tokenizer, max_input_len, max_seq_len)
    val_path = split_file_path(data_path, Split.VAL)
    val_dataset = LmDataset(
        val_path, tokenizer, max_input_len, max_seq_len, num_eval_examples
    )
    return train_dataset, val_dataset


def get_tokenizer(conf: dict[str, Any]) -> CodeLlamaTokenizer:
    model_name = get_required_arg("model_name", conf)
    seq_len = get_required_arg("max_seq_len", conf)
    tokenizer: CodeLlamaTokenizer = CodeLlamaTokenizer.from_pretrained(model_name)
    tokenizer.add_eos_token = True

    pad_token = "<PRE>"
    encoded_ids = tokenizer.encode(pad_token)
    assert len(encoded_ids) == 3
    assert encoded_ids[0] == tokenizer.bos_token_id
    assert encoded_ids[2] == tokenizer.eos_token_id

    tokenizer.pad_token = pad_token
    tokenizer.pad_token_id = encoded_ids[1]

    # tokenizer.padding_side = "right"
    # tokenizer.truncation_side = "right"
    # tokenizer.model_max_length = seq_len
    return tokenizer


def get_trainer(
    conf: dict[str, Any], local_rank: Optional[int], checkpoint_name: Optional[str]
) -> Trainer:
    max_seq_len = get_required_arg("max_seq_len", conf)
    max_input_len = get_required_arg("max_input_len", conf)

    print("\n\nBuilding Training Config...")
    training_args = get_training_args(conf, local_rank)
    print("\n\nRetrieving Tokenizer...")
    tokenizer = get_tokenizer(conf)

    print("\n\nRetrieving Model...")
    raw_model = get_model(conf)
    lora_config = get_lora_conf(conf)
    model = get_peft_model(raw_model, lora_config)

    print("\n\nConstructing Dataset...")
    train_dataset, val_dataset = get_datasets(
        conf, tokenizer, max_input_len, max_seq_len
    )

    print("\n\nBuilding Trainer...")
    return Trainer(
        model=model,
        args=training_args,
        train_dataset=train_dataset,
        eval_dataset=val_dataset,
        data_collator=train_dataset.collator,
        tokenizer=tokenizer,
    )


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
