
from typing import Optional, Iterable
import sys, os
os.environ["CUDA_VISIBLE_DEVICES"] = "3"

import jsonlines
from trl import SFTTrainer, DataCollatorForCompletionOnlyLM
from peft import LoraConfig
from transformers import (
    LlamaForCausalLM, CodeLlamaTokenizer,
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

DATA_PATH = "/home/ubuntu/coq-modeling/data/data-points-partial-split"

MODEL_NAME = "codellama/CodeLlama-7b-hf"
OUTPUT_LOC = "/home/ubuntu/coq-modeling/models/codellama-7b-hf-test"
TRAIN_BATCH_SIZE = 4
LEARNING_RATE = 1.41e-5
NUM_TRAIN_EPOCHS = 1
MAX_STEPS = -1
PEFT_LORA_R = 64
PEFT_LORA_ALPHA = 16
MAX_SEQ_LEN = 2 ** 9
GRADIENT_ACCUMULATION_STEPS = 2

DEFAULT_LOGGING_STEPS = 1
DEFAULT_SAVE_STEPS = 100
DEFAULT_SAVE_TOTAL_LIMIT = 10
DEFAULT_PUSH_TO_HUB = False
DEFAULT_HUB_MODEL_ID: Optional[str] = None
DEFAULT_LOG_WITH: Optional[str] = None

quantization_config = BitsAndBytesConfig(load_in_4bit=True)

model = LlamaForCausalLM.from_pretrained(
    MODEL_NAME, quantization_config=quantization_config,
)


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

def dataset_gen(dataset_path: str, split: str) -> Iterable[dict[str, str]]:
    file_path = split_file_path(dataset_path, split)
    with jsonlines.open(file_path, "r") as fin:
        for obj in fin:
            yield obj 

train_kwargs = {
    "dataset_path": DATA_PATH,
    "split": TRAIN_NAME,
}
val_kwargs = {
    "dataset_path": DATA_PATH,
    "split": VAL_NAME,
}
train_dataset = Dataset.from_generator(dataset_gen, gen_kwargs=train_kwargs)
val_dataset = Dataset.from_generator(dataset_gen, gen_kwargs=val_kwargs)


tokenizer = CodeLlamaTokenizer.from_pretrained(MODEL_NAME)
tokenizer.pad_token = tokenizer.eos_token
tokenizer.padding_side = "left"
tokenizer.truncation_side = "left"
tokenizer.model_max_length = MAX_SEQ_LEN 

# FROM HERE: https://huggingface.co/docs/trl/sft_trainer#train-on-completions-only
response_template = "<TACTIC>"
newline_response_template = f"\n{response_template}\n"
response_template_ids = tokenizer.encode(newline_response_template)[2:-1]
def formatting_examples_func(examples: list[dict[str, str]]) -> list[str]: 
    output_strs: list[str] = []
    for i in range(len(examples["input"])):
        example_in = examples["input"][i]
        example_out = examples["output"][i]
        collated_str = f"{example_in}{newline_response_template}{example_out}"
        output_strs.append(collated_str) 
    return output_strs

collator = DataCollatorForCompletionOnlyLM(response_template_ids, tokenizer=tokenizer)

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
    eval_dataset=val_dataset,
    formatting_func=formatting_examples_func,
    data_collator=collator,
    peft_config=peft_config,
    tokenizer=tokenizer,
)

trainer.train()



