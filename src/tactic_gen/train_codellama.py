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

from tactic_gen.lm_example import LmExample
from tactic_gen.codellama_data import LmDataset
from data_management.splits import Split, split2str, split_file_path
from data_management.create_lm_dataset import DATA_CONF_NAME


# This doc details how to finetune codellama:
# https://github.com/huggingface/trl/blob/main/examples/scripts/sft_trainer.py

# More ideas for arguments here:
# https://huggingface.co/docs/transformers/main_classes/trainer#transformers.TrainingArguments


def load_config(path: str) -> dict[str, Any]:
    with open(path, "r") as fin:
        conf = load(fin, Loader=Loader)
    assert type(conf) == dict
    assert all([type(s) == str for s in conf.keys()])
    return conf


def make_output_dir(conf: dict[str, Any]) -> None:
    output_dir = __get_required_arg("output_dir", conf)
    if os.path.exists(output_dir):
        time_since_created = time.time() - os.path.getctime(output_dir)
        two_mins = 120
        if time_since_created > two_mins:
            print(f"{output_dir} already exists.")
            exit(1)
    else:
        os.makedirs(output_dir)


TRAINING_CONF_NAME = "training_conf.yaml"
REQS_NAME = "requirements.txt"
GIT_NAME = "git.json"


def __copy_configs(conf_path: str, conf: dict[str, Any]) -> None:
    output_dir = __get_required_arg("output_dir", conf)
    data_path = __get_required_arg("data_path", conf)
    data_conf_loc = os.path.join(data_path, DATA_CONF_NAME)
    shutil.copy(conf_path, os.path.join(output_dir, TRAINING_CONF_NAME))
    shutil.copy(data_conf_loc, os.path.join(output_dir, DATA_CONF_NAME))
    reqs = subprocess.check_output([sys.executable, "-m", "pip", "freeze"])
    with open(os.path.join(output_dir, REQS_NAME), "wb") as fout:
        fout.write(reqs)
    commit = subprocess.check_output(["git", "rev-parse", "HEAD"])
    with open(os.path.join(output_dir, GIT_NAME), "wb") as fout:
        fout.write(commit)


def __get_required_arg(key: str, conf: dict[str, Any]) -> Any:
    if key not in conf:
        print(f"{key} is a required field in the configuration file.")
        exit(1)
    return conf[key]


def __get_optional_arg(key: str, conf: dict[str, Any], default: Any) -> Any:
    if key not in conf:
        print(f"{key} not found in configuration. Defaulting to {default}")
        return default
    return conf[key]


def get_training_args(
    conf: dict[str, Any], local_rank: Optional[int]
) -> TrainingArguments:
    return TrainingArguments(
        output_dir=__get_required_arg("output_dir", conf),
        per_device_train_batch_size=__get_required_arg(
            "per_device_train_batch_size", conf
        ),
        gradient_accumulation_steps=__get_optional_arg(
            "gradient_accumulation_steps", conf, 2
        ),
        optim="paged_adamw_8bit",
        learning_rate=__get_required_arg("learning_rate", conf),
        logging_steps=__get_required_arg("logging_steps", conf),
        num_train_epochs=__get_required_arg("num_train_epochs", conf),
        max_steps=__get_optional_arg("max_steps", conf, -1),
        save_steps=__get_required_arg("save_steps", conf),
        save_total_limit=__get_required_arg("save_total_limit", conf),
        evaluation_strategy="steps",
        eval_steps=__get_required_arg("eval_steps", conf),
        per_device_eval_batch_size=__get_required_arg(
            "per_device_eval_batch_size", conf
        ),
        eval_accumulation_steps=__get_optional_arg("eval_accumulation_steps", conf, 1),
        # deepspeed=__get_required_arg("deepspeed", conf),
        local_rank=(local_rank if local_rank else -1),
        ddp_find_unused_parameters=False,
    )


def get_lora_conf(conf: dict[str, Any]) -> LoraConfig:
    return LoraConfig(
        r=__get_required_arg("peft_lora_r", conf),
        lora_alpha=__get_required_arg("peft_lora_alpha", conf),
        bias="none",
        task_type="CAUSAL_LM",
    )


def get_model(conf: dict[str, Any]) -> LlamaForCausalLM:
    model_name = __get_required_arg("model_name", conf)
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
    data_path = __get_required_arg("data_path", conf)
    num_eval_examples = __get_optional_arg("num_eval_examples", conf, None)
    train_path = split_file_path(data_path, Split.TRAIN)
    train_dataset = LmDataset(train_path, tokenizer, max_input_len, max_seq_len)
    val_path = split_file_path(data_path, Split.VAL)
    val_dataset = LmDataset(
        val_path, tokenizer, max_input_len, max_seq_len, num_eval_examples
    )
    return train_dataset, val_dataset


def get_tokenizer(conf: dict[str, Any]) -> CodeLlamaTokenizer:
    model_name = __get_required_arg("model_name", conf)
    seq_len = __get_required_arg("max_seq_len", conf)
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


def get_trainer(conf: dict[str, Any], local_rank: Optional[int]) -> Trainer:
    max_seq_len = __get_required_arg("max_seq_len", conf)
    max_input_len = __get_required_arg("max_input_len", conf)

    print("\n\nBuilding Training Config...")
    training_args = get_training_args(conf, local_rank)
    print("\n\nRetrieving Tokenizer...")
    tokenizer = get_tokenizer(conf)
    print("\n\nRetrieving Model...")
    model = get_model(conf)

    lora_config = get_lora_conf(conf)
    lora_model = get_peft_model(model, lora_config)

    print("\n\nConstructing Dataset...")
    train_dataset, val_dataset = get_datasets(
        conf, tokenizer, max_input_len, max_seq_len
    )

    print("\n\nBuilding Trainer...")
    return Trainer(
        model=lora_model,
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
    trainer = get_trainer(conf, args.local_rank)
    train_from_checkpoint = "checkpoint_name" in conf
    if train_from_checkpoint:
        checkpoint_name = conf["checkpoint_name"]
        print(f"Training from checkpoint {checkpoint_name}")
        transformers.logging.set_verbosity_info()
        trainer.train(checkpoint_name)
    else:
        make_output_dir(conf)
        __copy_configs(args.yaml_config, conf)
        print("Training from scratch")
        trainer.train()
