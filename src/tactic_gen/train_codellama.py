
from typing import Optional, Iterable, Any
import sys, os
import shutil
import re
import argparse
import functools

from yaml import load, Loader
import jsonlines
from trl import SFTTrainer, DataCollatorForCompletionOnlyLM
from peft import LoraConfig
from transformers import (
    LlamaForCausalLM, CodeLlamaTokenizer,
    BitsAndBytesConfig, TrainingArguments)
import torch
from datasets import Dataset
from evaluate import EvaluationModule
import numpy as np 

from tactic_gen.lm_example import LmExample
from data_management.create_lm_dataset import split_file_path
from data_management.split_raw_data import TRAIN_NAME, VAL_NAME


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

CONF_NAME = "training_conf.yaml"
def __copy_config(conf_path: str, conf: dict[str, Any]) -> None:
    output_dir = __get_required_arg("output_dir", conf)
    if os.path.exists(output_dir):
        print(f"{output_dir} already exists.")
        exit(1)
    os.makedirs(output_dir)
    shutil.copy(conf_path, os.path.join(output_dir, CONF_NAME))

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


def get_training_args(conf: dict[str, Any]) -> TrainingArguments:
    return TrainingArguments(
        output_dir = __get_required_arg(
            "output_dir", conf),
        per_device_train_batch_size = __get_required_arg(
            "per_device_train_batch_size", conf),
        gradient_accumulation_steps = __get_optional_arg(
            "gradient_accumulation_steps", conf, 2),
        learning_rate = __get_required_arg(
            "learning_rate", conf),
        logging_steps = __get_required_arg(
            "logging_steps", conf),
        num_train_epochs = __get_required_arg(
            "num_train_epochs", conf),
        max_steps = __get_optional_arg(
            "max_steps", conf, -1),
        save_steps = __get_required_arg(
            "save_steps", conf),
        save_total_limit = __get_required_arg(
            "save_total_limit", conf),
        evaluation_strategy = "steps",
        eval_steps = __get_required_arg(
            "eval_steps", conf),
        per_device_eval_batch_size = __get_required_arg(
            "per_device_eval_batch_size", conf),
        eval_accumulation_steps= __get_optional_arg(
            "eval_accumulation_steps", conf, 1)
        )

def get_peft_conf(conf: dict[str, Any]) -> LoraConfig:
    return LoraConfig(
        r= __get_required_arg("peft_lora_r", conf),
        lora_alpha= __get_required_arg("peft_lora_alpha", conf),
        bias="none",
        task_type="CAUSAL_LM",
    )  

def get_model(conf: dict[str, Any]) -> LlamaForCausalLM:
    model_name = __get_required_arg("model_name", conf)
    quantization_config = BitsAndBytesConfig(load_in_4bit=True)
    model = LlamaForCausalLM.from_pretrained(
        model_name, quantization_config=quantization_config
    )
    assert type(model) == LlamaForCausalLM
    return model


def dataset_gen(dataset_path: str, split: str, limit: int) -> Iterable[dict[str, str]]:
    file_path = split_file_path(dataset_path, split)
    with jsonlines.open(file_path, "r") as fin:
        num_examples = 0
        for obj in fin:
            if limit > 0 and num_examples >= limit:
                break
            yield obj 
            num_examples += 1

# FROM HERE: https://huggingface.co/docs/trl/sft_trainer#train-on-completions-only
RESPONSE_TEMPLATE = "<TACTIC>"
NEWLINE_RESPONSE_TEMPLATE = f"\n{RESPONSE_TEMPLATE}\n"


def collate_input(tokenizer: CodeLlamaTokenizer, max_input_len: int, input: str) -> str:
    whole_input_string = f"{input}{NEWLINE_RESPONSE_TEMPLATE}"
    input_suffix = tokenizer.tokenize(whole_input_string)[(-1 * max_input_len):]
    ret_str = tokenizer.convert_tokens_to_string(input_suffix)
    assert type(ret_str) == str
    return ret_str 


# def formatting_examples_func(tokenizer: CodeLlamaTokenizer,
#                              max_input_len: int, 
#                              examples: dict[str, list[str]]) -> list[str]: 
#     """NOTE: THE TYPE ANNOTATION FOR EXAMPLES MAY NOT BE EXACTLY RIGHT BUT
#        MATCHES MY MENTAL MODEL OF THE DATA STRUCTURE"""
#     output_strs: list[str] = []
#     for i in range(len(examples["input"])):
#         example_in = examples["input"][i]
#         example_out = examples["output"][i]
#         collated_input = collate_input(tokenizer, max_input_len, example_in)
#         collated_str = f"{collated_input}{example_out}"
#         output_strs.append(collated_str) 
#     return output_strs


def formatting_examples_func(examples: dict[str, list[str]], **kwargs: Any) -> list[str]: 
    """NOTE: THE TYPE ANNOTATION FOR EXAMPLES MAY NOT BE EXACTLY RIGHT BUT
       MATCHES MY MENTAL MODEL OF THE DATA STRUCTURE"""
    assert "tokenizer" in kwargs
    assert "max_input_len" in kwargs
    tokenizer = kwargs["tokenizer"]
    max_input_len = kwargs["max_input_len"]
    output_strs: list[str] = []
    for i in range(len(examples["input"])):
        example_in = examples["input"][i]
        example_out = examples["output"][i]
        collated_input = collate_input(tokenizer, max_input_len, example_in)
        collated_str = f"{collated_input}{example_out}"
        output_strs.append(collated_str) 
    return output_strs



def get_datasets(conf: dict[str, Any]) -> tuple[Dataset, Dataset]:
    data_path = __get_required_arg("data_path", conf)
    num_eval_examples = __get_optional_arg("num_eval_examples", conf, -1)
    train_kwargs = {
        "dataset_path": data_path,
        "split": TRAIN_NAME,
        "limit": -1,
    }
    val_kwargs = {
        "dataset_path": data_path,
        "split": VAL_NAME,
        "limit": num_eval_examples,
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
    tokenizer.padding_side = "right"
    tokenizer.truncation_side = "right"
    tokenizer.model_max_length = seq_len 
    return tokenizer


def get_trainer(conf: dict[str, Any]) -> SFTTrainer:
    max_seq_len = __get_required_arg("max_seq_len", conf)
    max_input_len = __get_required_arg("max_input_len", conf)

    print("\n\nBuilding Training Config...")
    training_args = get_training_args(conf)
    print("\n\nRetrieving Model...")
    model = get_model(conf)
    print("\n\nRetrieving Tokenizer...")
    tokenizer = get_tokenizer(conf)
    peft_config = get_peft_conf(conf)

    print("\n\nConstructing Dataset...")
    train_dataset, val_dataset = get_datasets(conf)

    response_template_ids = tokenizer.encode(NEWLINE_RESPONSE_TEMPLATE)[2:-1]
    collator = DataCollatorForCompletionOnlyLM(
        response_template_ids, tokenizer=tokenizer)

    formatting_func = functools.partial(formatting_examples_func, 
                                        tokenizer=tokenizer,
                                        max_input_len=max_input_len)

    print("\n\nBuilding Trainer...")
    return SFTTrainer(
        model=model,
        args=training_args,
        max_seq_length=max_seq_len,
        train_dataset=train_dataset,
        eval_dataset=val_dataset,
        formatting_func=formatting_func,
        data_collator=collator,
        peft_config=peft_config,
        tokenizer=tokenizer,
    )

if __name__=="__main__":
    parser = argparse.ArgumentParser(description="Train code llama by providing a .yaml config file. As an example, see src/tactic_gen/confs/basic_train.yaml")
    parser.add_argument("yaml_config", help="yaml config file to use for training.")
    args = parser.parse_args(sys.argv[1:])
    conf = load_config(args.yaml_config)
    __copy_config(args.yaml_config, conf)
    trainer = get_trainer(conf)
    trainer.train()



