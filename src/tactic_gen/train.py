
from typing import Optional, Iterable
import sys, os

import jsonlines
from trl import SFTTrainer, DataCollatorForCompletionOnlyLM
from peft import LoraConfig
from transformers import (
    AutoTokenizer, AutoModelForCausalLM,
    BitsAndBytesConfig, TrainingArguments)
import torch
import argparse
from datasets import Dataset

from data_management.lm_example import LmExample
from data_management.create_lm_dataset import split_file_path
from data_management.split_raw_data import TRAIN_NAME, VAL_NAME

# This doc details how to finetune codellama:
# https://github.com/huggingface/trl/blob/main/examples/scripts/sft_trainer.py


DATA_PATH = "data/data-points-partial-split"

MODEL_NAME = "codellama/CodeLlama-7b-hf"
TRAIN_WITH_DEVICE = 7
OUTPUT_LOC = "/home/ubuntu/coq-modeling/models/codellama-7b-hf-test"
TRAIN_BATCH_SIZE = 4
LEARNING_RATE = 1.41e-5
NUM_TRAIN_EPOCHS = 1
MAX_STEPS = -1
PEFT_LORA_R = 64
PEFT_LORA_ALPHA = 16
MAX_SEQ_LEN = 512
GRADIENT_ACCUMULATION_STEPS = 2



DEFAULT_LOGGING_STEPS = 1
DEFAULT_SAVE_STEPS = 100
DEFAULT_SAVE_TOTAL_LIMIT = 10
DEFAULT_PUSH_TO_HUB = False
DEFAULT_HUB_MODEL_ID: Optional[str] = None
DEFAULT_LOG_WITH: Optional[str] = None

training_args = TrainingArguments(
    output_dir=OUTPUT_LOC,
    per_device_train_batch_size=TRAIN_BATCH_SIZE,
    gradient_accumulation_steps=GRADIENT_ACCUMULATION_STEPS,
    learning_rate=LEARNING_RATE,
    logging_steps=DEFAULT_LOGGING_STEPS,
    num_train_epochs=NUM_TRAIN_EPOCHS,
    max_steps=MAX_STEPS,
    report_to=DEFAULT_LOG_WITH,
    save_steps=DEFAULT_SAVE_STEPS,
    save_total_limit=DEFAULT_SAVE_TOTAL_LIMIT,
    push_to_hub=DEFAULT_PUSH_TO_HUB,
    hub_model_id=DEFAULT_HUB_MODEL_ID,
)

def dataset_gen(dataset_path: str, split: str) -> Iterable[LmExample]:
    file_path = split_file_path(dataset_path, split)
    with jsonlines.open(file_path, "r") as fin:
        for obj in fin:
            yield LmExample.from_json(obj)

train_generator = dataset_gen(DATA_PATH, TRAIN_NAME)
val_generator = dataset_gen(DATA_PATH, VAL_NAME)
train_dataset = Dataset.from_generator(train_generator)
val_dataset = Dataset.from_generator(val_generator)


# FROM HERE: https://huggingface.co/docs/trl/sft_trainer#train-on-completions-only
response_template = " <TACTIC>"
def formatting_examples_func(examples: list[LmExample]) -> list[str]: 
    output_strs: list[str] = []
    for example in examples:
        collated_str = f"{example.input}\n{response_template} {example.output}"
        output_strs.append(collated_str) 
    return output_strs

tokenizer = AutoTokenizer.from_pretrained(MODEL_NAME)
collator = DataCollatorForCompletionOnlyLM(response_template, tokenizer=tokenizer)

torch.cuda.set_device(TRAIN_WITH_DEVICE)
quantization_config = BitsAndBytesConfig(load_in_4bit=True)
model = AutoModelForCausalLM.from_pretrained(
    MODEL_NAME, quantization_config=quantization_config,
)

peft_config = LoraConfig(
    r=PEFT_LORA_R,
    lora_alpha=PEFT_LORA_ALPHA,
    bias="none",
    task_type="CAUSAL_LM",
) 

trainer = SFTTrainer(
    model=model,
    args=training_args,
    max_seq_length=MAX_SEQ_LEN,
    train_dataset=train_dataset,
    val_dataset=val_dataset,
    formatting_func=formatting_examples_func,
    data_collator=collator,
)

trainer.train()



