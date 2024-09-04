from __future__ import annotations

import re
import os
import pickle
import random
import functools
from typing import Any, Optional
from pathlib import Path
import json
from dataclasses import dataclass

# from datasets import Dataset
from torch.utils.data import Dataset

from transformers import AutoTokenizer, PreTrainedTokenizer, BatchEncoding
from trl import DataCollatorForCompletionOnlyLM
import jsonlines
from data_management.dataset_file import DatasetFile
from data_management.sentence_db import SentenceDB
from data_management.jsonl_utils import ExampleDB
from data_management.line_dict import LineDict
from data_management.splits import Split
from data_management.dataset_file import DPCache, StepID

from lemma_gen.lemma_example import LemmaExample

from util.train_utils import allocate_tokens
from util.util import get_basic_logger
from util.shuffled_idx import ShuffledIndex
from util.constants import DATA_POINTS_NAME

_logger = get_basic_logger(__name__)

# FROM HERE: https://huggingface.co/docs/trl/sft_trainer#train-on-completions-only
RESPONSE_TEMPLATE = "[LEMMA]"
NEWLINE_RESPONSE_TEMPLATE = f"\n{RESPONSE_TEMPLATE}\n"

# __test_lm_json = {
#     "target": "Theorem app_nil_r : forall l : list X, l ++ [] = l.",
#     "current_script": "Theorem rev_app : forall x l, rev l ++ [x] = rev (x::l).\nProof.\n  intros.",
#     "current_state": "x: X\nl: list X\n\nrev l ++ [x] = rev (x :: l)",
#     "next_steps": ["\n  simpl.", " reflexivity.", "\nQed."],
#     "premises": [
#         # "Theorem rev_app_distr : forall l l' : list X, rev (l ++ l') = rev l' ++ rev l.",
#         # "Theorem app_nil_r : forall l : list X, l ++ [] = l.",
#         "Theorem app_assoc : forall l m n : list X, l ++ m ++ n = (l ++ m) ++ n.",
#         "Theorem app_length : forall l l' : list X, length l + length l' = length (l ++ l').",
#     ],
# }

# TEST_LEMMA_EXAMPLE = LemmaExample.from_json(__test_lm_json)


def whole_number_allocate(
    tokenizer: PreTrainedTokenizer,
    ss: list[str],
    allowance: int,
) -> list[str]:
    cur_allowance = allowance
    allowed_passages: list[str] = []
    for s in ss:
        s_toks = tokenizer.tokenize(s)
        cur_allowance -= len(s_toks)
        if cur_allowance < 0:
            break
        allowed_passages.append(s)
    return allowed_passages


def allocate_and_fmt(
    tokenizer: PreTrainedTokenizer,
    ss: Optional[list[str]],
    allowance: int,
    reverse: bool = True,
) -> str:
    if ss is None:
        return ""
    allowed_passages = whole_number_allocate(tokenizer, ss, allowance)
    if reverse:
        return "\n".join(allowed_passages[::-1])
    else:
        return "\n".join(allowed_passages)


@dataclass
class BasicCollatorConf:
    script_tokens: int
    state_tokens: int
    out_tokens: int
    whole_proof: bool
    ALIAS = "basic"

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> BasicCollatorConf:
        return cls(
            yaml_data["script_tokens"],
            yaml_data["state_tokens"],
            yaml_data["out_tokens"],
            yaml_data.get("whole_proof", False),
        )


@dataclass
class BasicCollator:
    script_tokens: int
    state_tokens: int
    out_tokens: int

    STATE_SEP = "\n[STATE]\n"
    SCRIPT_SEP = "\n[SCRIPT]\n"

    def collate_input(
        self, tokenizer: PreTrainedTokenizer, example: LemmaExample
    ) -> str:
        state_str, _ = allocate_tokens(
            tokenizer, example.current_state, self.state_tokens
        )
        script_str, _ = allocate_tokens(
            tokenizer, example.current_script, self.script_tokens
        )
        combined_str = (
            self.STATE_SEP
            + state_str
            + self.SCRIPT_SEP
            + script_str
            + NEWLINE_RESPONSE_TEMPLATE
        )
        return combined_str

    def collate(self, tokenizer: PreTrainedTokenizer, example: LemmaExample) -> str:
        input_str = self.collate_input(tokenizer, example)
        target = example.target
        out_str, _ = allocate_tokens(
            tokenizer, target, self.out_tokens, truncate_front=False
        )
        combined_str = input_str + out_str
        return combined_str

    @classmethod
    def from_conf(cls, conf: BasicCollatorConf) -> BasicCollator:
        return cls(
            conf.script_tokens,
            conf.state_tokens,
            conf.out_tokens,
        )


@dataclass
class PremiseCollatorConf:
    script_tokens: int
    state_tokens: int
    premise_tokens: int
    out_tokens: int
    ALIAS = "premise"

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> PremiseCollatorConf:
        return cls(
            yaml_data["script_tokens"],
            yaml_data["state_tokens"],
            yaml_data["premise_tokens"],
            yaml_data["out_tokens"],
        )


@dataclass
class PremiseCollator:
    script_tokens: int
    state_tokens: int
    premise_tokens: int
    out_tokens: int

    STATE_SEP = "\n[STATE]\n"
    SCRIPT_SEP = "\n[SCRIPT]\n"
    PREMISE_SEP = "\n[PREMISES]\n"

    def collate_input(
        self, tokenizer: PreTrainedTokenizer, example: LemmaExample
    ) -> str:
        premise_str = allocate_and_fmt(
            tokenizer, example.relevant_lemmas, self.premise_tokens
        )
        state_str, _ = allocate_tokens(
            tokenizer, example.current_state, self.state_tokens
        )
        script_str, _ = allocate_tokens(
            tokenizer, example.current_script, self.script_tokens
        )
        combined_str = (
            self.PREMISE_SEP
            + premise_str
            + self.STATE_SEP
            + state_str
            + self.SCRIPT_SEP
            + script_str
            + NEWLINE_RESPONSE_TEMPLATE
        )
        return combined_str

    def collate(self, tokenizer: PreTrainedTokenizer, example: LemmaExample) -> str:
        input_str = self.collate_input(tokenizer, example)
        target = example.target
        out_str, _ = allocate_tokens(
            tokenizer, target, self.out_tokens, truncate_front=False
        )
        combined_str = input_str + out_str
        return combined_str

    @classmethod
    def from_conf(cls, conf: PremiseCollatorConf) -> PremiseCollator:
        return cls(
            conf.script_tokens, conf.state_tokens, conf.premise_tokens, conf.out_tokens
        )


ExampleCollator = BasicCollator | PremiseCollator

ExampleCollatorConf = BasicCollatorConf | PremiseCollatorConf


def example_collator_conf_from_yaml(yaml_data: Any) -> ExampleCollatorConf:
    attempted_alias = yaml_data["alias"]
    match attempted_alias:
        case BasicCollatorConf.ALIAS:
            return BasicCollatorConf.from_yaml(yaml_data)
        case PremiseCollatorConf.ALIAS:
            return PremiseCollatorConf.from_yaml(yaml_data)
        case _:
            raise ValueError(f"Could not find example collator: {attempted_alias}")


def example_collator_from_conf(conf: ExampleCollatorConf) -> ExampleCollator:
    match conf:
        case BasicCollatorConf():
            return BasicCollator.from_conf(conf)
        case PremiseCollatorConf():
            return PremiseCollator.from_conf(conf)


class LemmaDataset(Dataset):
    def __init__(
        self,
        data_path: Path,
        tokenizer: PreTrainedTokenizer,
        example_collator: ExampleCollator,
        hard_seq_len: int,
        max_n_examples: Optional[int] = None,
    ) -> None:
        super(LemmaDataset, self).__init__()
        self.edb = ExampleDB.load(data_path)
        __shuffled_list = list(range(self.edb.size()))
        random.seed(0)
        random.shuffle(__shuffled_list)
        self.edb_map = dict(zip(range(self.edb.size()), __shuffled_list))
        self.collator = DataCollatorForCompletionOnlyLM(
            response_template=NEWLINE_RESPONSE_TEMPLATE,
            tokenizer=tokenizer,
            mlm=False,
        )
        self.hard_seq_len = hard_seq_len
        self.tokenizer = tokenizer
        self.example_collator = example_collator
        self.max_n_examples = max_n_examples

    def __len__(self) -> int:
        if self.max_n_examples is not None:
            return self.max_n_examples
        return self.edb.size()

    def __getitem__(self, idx: int) -> Any:
        target_idx = self.edb_map[idx]
        target_lemma_example = LemmaExample.from_json(
            json.loads(self.edb.retrieve(target_idx + 1))
        )
        clean_example = self.example_collator.collate(
            self.tokenizer, target_lemma_example
        )
        return self.tokenizer(
            clean_example,
            max_length=self.hard_seq_len,
            truncation=True,
            padding="max_length",
        )


def get_tokenizer(model_name: str, add_eos=True) -> PreTrainedTokenizer:
    tokenizer = AutoTokenizer.from_pretrained(model_name)
    tokenizer.padding_side = "right"
    tokenizer.truncation_side = "left"
    if add_eos:
        tokenizer.add_eos_token = True
    else:
        tokenizer.add_eos_token = False
    assert tokenizer.pad_token_id != tokenizer.eos_token_id
    if model_name.startswith("codellama") or model_name.startswith(
        "openai-community/gpt"
    ):
        tokenizer.add_special_tokens({"pad_token": "[PAD]"})
        # print("ADDING PAD TOKEN")
        # tokenizer.add_eos_token = True
        # pad_token = "<PRE>"
        # encoded_ids = tokenizer.encode(pad_token)
        # assert len(encoded_ids) == 3
        # assert encoded_ids[0] == tokenizer.bos_token_id
        # assert encoded_ids[2] == tokenizer.eos_token_id

        # tokenizer.pad_token = pad_token
        # tokenizer.pad_token_id = encoded_ids[1]
    return tokenizer
