from __future__ import annotations
from typing import Any, Optional
from tactic_gen.lm_example import LmExample
from tactic_gen.train_fid import get_model, get_tokenizer, get_datasets
from tactic_gen.fid_data import FidDataset
from tactic_gen.fid_prime_model import FiDT5
from transformers import T5ForConditionalGeneration
from transformers import T5Tokenizer, CodeLlamaTokenizer
import torch
from pathlib import Path
import ipdb

MODEL_NAME = "google-t5/t5-small"

t5 = T5ForConditionalGeneration.from_pretrained(MODEL_NAME)
t5.config.n_passages = 8
fid_model = FiDT5(t5.config)
fid_model.load_t5(t5.state_dict())
fid_model.cuda()

tokenizer = T5Tokenizer.from_pretrained(MODEL_NAME)

test_example = LmExample("hi", "there")

dataset = FidDataset(None, tokenizer, 448, 64, 8)

test_batch = dataset.collate([test_example])

# outputs = fid_model(
#     test_batch["input_ids"].cuda(),
#     test_batch["attention_mask"].cuda(),
#     test_batch["labels"].cuda(),
# )

outputs = fid_model.generate(
    test_batch["input_ids"].cuda(),
    test_batch["attention_mask"].cuda(),
    64,
    return_dict_in_generate=True,
    output_scores=True,
)


# "/home/ubuntu/coq-modeling/venv/lib/python3.10/site-packages/transformers/models/t5/modeling_t5.py:560"
