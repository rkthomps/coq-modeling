from __future__ import annotations
from typing import Any, Optional
from tactic_gen.lm_example import LmExample
from tactic_gen.train_fid import get_model, get_tokenizer, get_datasets
from tactic_gen.fid_data import FidDataset
from tactic_gen.fid_combined import FidCombined, FidCombinedConfig
from transformers import T5ForConditionalGeneration
from transformers import T5Tokenizer, CodeLlamaTokenizer
import torch
from pathlib import Path
import ipdb


MODEL_NAME = "google-t5/t5-small"
# t5 = T5ForConditionalGeneration.from_pretrained(MODEL_NAME)
# n_passages = 8
# custom_config = FidCombinedConfig.from_t5_config(n_passages, t5.config)
# model = FidCombined(custom_config)
# model.cuda()

pretrained_loc = "models/t5-fid-small-test/checkpoint-20"
model = FidCombined.from_pretrained(pretrained_loc)
model.cuda()
print("model num passages:", model.config.n_passages)


tokenizer = T5Tokenizer.from_pretrained(MODEL_NAME)
test_example = LmExample("hi", "there")
dataset = FidDataset(None, tokenizer, 448, 64, 8)
test_batch = dataset.collate([test_example])

# outputs = model(
#     test_batch["input_ids"].cuda(),
#     test_batch["attention_mask"].cuda(),
#     test_batch["labels"].cuda(),
# )

outputs = model.generate(
    input_ids=test_batch["input_ids"].cuda(),
    attention_mask=test_batch["attention_mask"].cuda(),
    max_length=40,
    # test_batch["labels"].cuda(),
)
print(outputs)


# outputs = fid_model.generate(
#     test_batch["input_ids"].cuda(),
#     test_batch["attention_mask"].cuda(),
#     64,
#     return_dict_in_generate=True,
#     output_scores=True,
# )


# "/home/ubuntu/coq-modeling/venv/lib/python3.10/site-packages/transformers/models/t5/modeling_t5.py:560"
