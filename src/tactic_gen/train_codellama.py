from typing import Optional, Iterable, Generator, Any
import sys, os
import shutil
import re
import time
import argparse
import functools

from yaml import load, Loader
import jsonlines
from trl import SFTTrainer, DataCollatorForCompletionOnlyLM
from peft import LoraConfig
import transformers
from transformers import (
    LlamaForCausalLM,
    CodeLlamaTokenizer,
    BitsAndBytesConfig,
    TrainingArguments,
    HfArgumentParser,
    BatchEncoding,
)
import torch
from datasets import Dataset
import numpy as np

from tactic_gen.lm_example import LmExample
from data_management.split_raw_data import TRAIN_NAME, VAL_NAME, split_file_path
from data_management.create_lm_dataset import DATA_CONF_NAME


# This doc details how to finetune codellama:
# https://github.com/huggingface/trl/blob/main/examples/scripts/sft_trainer.py

# More ideas for arguments here:
# https://huggingface.co/docs/transformers/main_classes/trainer#transformers.TrainingArguments


def load_config(path: str) -> dict[str, Any]:
    with open(path, "r") as fin:
        conf = load(fin, Loader=Loader)
    assert type(conf) == dict
    assert all(type(s) == str for s in conf.keys())
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


def __copy_configs(conf_path: str, conf: dict[str, Any]) -> None:
    output_dir = __get_required_arg("output_dir", conf)
    data_path = __get_required_arg("data_path", conf)
    data_conf_loc = os.path.join(data_path, DATA_CONF_NAME)
    shutil.copy(conf_path, os.path.join(output_dir, TRAINING_CONF_NAME))
    shutil.copy(data_conf_loc, os.path.join(output_dir, DATA_CONF_NAME))


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
        deepspeed=__get_required_arg("deepspeed", conf),
        local_rank=(local_rank if local_rank else -1),
    )


def get_peft_conf(conf: dict[str, Any]) -> LoraConfig:
    return LoraConfig(
        r=__get_required_arg("peft_lora_r", conf),
        lora_alpha=__get_required_arg("peft_lora_alpha", conf),
        bias="none",
        task_type="CAUSAL_LM",
    )


def get_model(conf: dict[str, Any]) -> LlamaForCausalLM:
    model_name = __get_required_arg("model_name", conf)
    quantization_config = BitsAndBytesConfig(
        load_in_4bit=True, bnb_4bit_compute_dtype=torch.float16
    )
    model = LlamaForCausalLM.from_pretrained(
        model_name, quantization_config=quantization_config
    )
    assert type(model) == LlamaForCausalLM
    return model


def dataset_gen(
    dataset_path: str,
    split: str,
    limit: int,
    max_input_len: int,
    max_seq_len: int,
    tokenizer: CodeLlamaTokenizer,
) -> Generator[dict[str, str], None, None]:
    file_path = split_file_path(dataset_path, split)
    with jsonlines.open(file_path, "r") as fin:
        num_examples = 0
        for obj in fin:
            if limit > 0 and num_examples >= limit:
                break
            new_in, new_out = collate_example(
                tokenizer, max_input_len, max_seq_len, obj["input"], obj["output"]
            )
            new_str = f"{new_in}{new_out}"
            yield {"text": new_str}
            num_examples += 1


# FROM HERE: https://huggingface.co/docs/trl/sft_trainer#train-on-completions-only
RESPONSE_TEMPLATE = "<TACTIC>"
NEWLINE_RESPONSE_TEMPLATE = f"\n{RESPONSE_TEMPLATE}\n"


def collate_example(
    tokenizer: CodeLlamaTokenizer,
    max_input_len: int,
    max_seq_len: int,
    input: str,
    output: str,
    response_template: str = NEWLINE_RESPONSE_TEMPLATE,
) -> tuple[str, str]:
    whole_input_string = f"{input}{response_template}"
    input_suffix = tokenizer.encode(whole_input_string)[(-1 * max_input_len) :]
    final_input_str = tokenizer.decode(input_suffix, skip_special_tokens=True)
    remaining_toks = max_seq_len - len(input_suffix)
    output_prefix = tokenizer.encode(output)[:remaining_toks]
    final_output_str = tokenizer.decode(output_prefix)
    return final_input_str, final_output_str


def get_datasets(
    conf: dict[str, Any],
    tokenizer: CodeLlamaTokenizer,
    max_input_len: int,
    max_seq_len: int,
) -> tuple[Dataset, Dataset]:
    data_path = __get_required_arg("data_path", conf)
    num_eval_examples = __get_optional_arg("num_eval_examples", conf, -1)
    train_kwargs = {
        "dataset_path": data_path,
        "split": TRAIN_NAME,
        "limit": -1,
        "tokenizer": tokenizer,
        "max_input_len": max_input_len,
        "max_seq_len": max_seq_len,
    }
    val_kwargs = {
        "dataset_path": data_path,
        "split": VAL_NAME,
        "limit": num_eval_examples,
        "tokenizer": tokenizer,
        "max_input_len": max_input_len,
        "max_seq_len": max_seq_len,
    }
    train_dataset = Dataset.from_generator(dataset_gen, gen_kwargs=train_kwargs)
    val_dataset = Dataset.from_generator(dataset_gen, gen_kwargs=val_kwargs)
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


def get_trainer(conf: dict[str, Any], local_rank: Optional[int]) -> SFTTrainer:
    max_seq_len = __get_required_arg("max_seq_len", conf)
    max_input_len = __get_required_arg("max_input_len", conf)

    print("\n\nBuilding Training Config...")
    training_args = get_training_args(conf, local_rank)
    print("\n\nRetrieving Model...")
    model = get_model(conf)
    print("\n\nRetrieving Tokenizer...")
    tokenizer = get_tokenizer(conf)
    peft_config = get_peft_conf(conf)

    print("\n\nConstructing Dataset...")
    train_dataset, val_dataset = get_datasets(
        conf, tokenizer, max_input_len, max_seq_len
    )

    response_template_ids = tokenizer.encode(NEWLINE_RESPONSE_TEMPLATE)[2:-1]
    collator = DataCollatorForCompletionOnlyLM(
        response_template_ids, tokenizer=tokenizer
    )

    print("\n\nBuilding Trainer...")
    return SFTTrainer(
        model=model,
        args=training_args,
        max_seq_length=max_seq_len,
        train_dataset=train_dataset,
        eval_dataset=val_dataset,
        data_collator=collator,
        peft_config=peft_config,
        dataset_text_field="text",
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
    make_output_dir(conf)
    trainer = get_trainer(conf, args.local_rank)
    train_from_checkpoint = "checkpoint_name" in conf
    if train_from_checkpoint:
        checkpoint_name = conf["checkpoint_name"]
        print(f"Training from checkpoint {checkpoint_name}")
        transformers.logging.set_verbosity_info()
        trainer.train(checkpoint_name)
    else:
        __copy_configs(args.yaml_config, conf)
        print("Training from scratch")
        trainer.train()
