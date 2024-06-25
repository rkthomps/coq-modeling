from __future__ import annotations

import re
import random
from typing import Any, Optional
from pathlib import Path
import json
from dataclasses import dataclass

# from datasets import Dataset
from torch.utils.data import Dataset

from transformers import PreTrainedTokenizer, BatchEncoding
from trl import DataCollatorForCompletionOnlyLM
import jsonlines
from data_management.jsonl_utils import ExampleDB

from tactic_gen.lm_example import LmExample
from util.train_utils import allocate_tokens
from util.util import get_basic_logger

_logger = get_basic_logger(__name__)

# FROM HERE: https://huggingface.co/docs/trl/sft_trainer#train-on-completions-only
RESPONSE_TEMPLATE = "[TACTIC]"
NEWLINE_RESPONSE_TEMPLATE = f"\n{RESPONSE_TEMPLATE}\n"

__test_lm_json = {
    "proof_script": "Theorem rev_app : forall x l, rev l ++ [x] = rev (x::l).\nProof.\n  intros.",
    "proof_state": "x: X\nl: list X\n\nrev l ++ [x] = rev (x :: l)",
    "next_steps": ["\n  simpl.", " reflexivity.", "\nQed."],
    "proofs": [
        "Theorem rev_app_distr : forall l l' : list X, rev (l ++ l') = rev l' ++ rev l.\nProof.\n  intros.\n  induction l. destruct l'.\n    simpl. reflexivity.\n    simpl. rewrite app_nil_r. reflexivity.\n    simpl. rewrite IHl. rewrite app_assoc. reflexivity.\nQed.",
        "Theorem app_nil_r : forall l : list X, l ++ [] = l.\nProof.\n  intros.\n  induction l.\n    simpl. reflexivity.\n    simpl. rewrite IHl. reflexivity.\nQed.",
        "Theorem app_assoc : forall l m n : list X, l ++ m ++ n = (l ++ m) ++ n.\nProof.\n  intros.\n  induction l. destruct m. destruct n.\n    simpl. reflexivity.\n    simpl. reflexivity.\n    simpl. reflexivity.\n    simpl. rewrite IHl. reflexivity.\nQed.",
        "Theorem app_length : forall l l' : list X, length l + length l' = length (l ++ l').\nProof.\n  intros.\n  induction l. destruct l'.\n    simpl. reflexivity.\n    simpl. reflexivity.\n    simpl. rewrite IHl. reflexivity.\nQed.",
    ],
    "premises": [
        "Theorem rev_app_distr : forall l l' : list X, rev (l ++ l') = rev l' ++ rev l.",
        "Theorem app_nil_r : forall l : list X, l ++ [] = l.",
        "Theorem app_assoc : forall l m n : list X, l ++ m ++ n = (l ++ m) ++ n.",
        "Theorem app_length : forall l l' : list X, length l + length l' = length (l ++ l').",
    ],
}

TEST_LM_EXAMPLE = LmExample.from_json(__test_lm_json)


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
    tokenizer: PreTrainedTokenizer, ss: Optional[list[str]], allowance: int
) -> str:
    if ss is None:
        return ""
    allowed_passages = whole_number_allocate(tokenizer, ss, allowance)
    return "\n".join(allowed_passages[::-1])


@dataclass
class BasicCollator:
    script_tokens: int
    state_tokens: int
    out_tokens: int

    ALIAS = "basic"
    STATE_SEP = "\n[STATE]\n"
    SCRIPT_SEP = "\n[SCRIPT]\n"

    def collate_input(self, tokenizer: PreTrainedTokenizer, example: LmExample) -> str:
        state_str, _ = allocate_tokens(
            tokenizer, example.proof_state, self.state_tokens
        )
        script_str, _ = allocate_tokens(
            tokenizer, example.proof_script, self.script_tokens
        )
        combined_str = (
            self.STATE_SEP
            + state_str
            + self.SCRIPT_SEP
            + script_str
            + NEWLINE_RESPONSE_TEMPLATE
        )
        return combined_str

    def collate(self, tokenizer: PreTrainedTokenizer, example: LmExample) -> str:
        input_str = self.collate_input(tokenizer, example)
        out_str, _ = allocate_tokens(
            tokenizer, example.next_steps[0], self.out_tokens, truncate_front=False
        )
        combined_str = input_str + out_str
        return combined_str

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> BasicCollator:
        return cls(
            yaml_data["script_tokens"],
            yaml_data["state_tokens"],
            yaml_data["out_tokens"],
        )


@dataclass
class PremiseCollator:
    ALIAS = "premise"
    script_tokens: int
    state_tokens: int
    premise_tokens: int
    out_tokens: int

    STATE_SEP = "\n[STATE]\n"
    SCRIPT_SEP = "\n[SCRIPT]\n"
    PREMISE_SEP = "\n[PREMISES]\n"

    def collate_input(self, tokenizer: PreTrainedTokenizer, example: LmExample) -> str:
        premise_str = allocate_and_fmt(tokenizer, example.premises, self.premise_tokens)
        state_str, _ = allocate_tokens(
            tokenizer, example.proof_state, self.state_tokens
        )
        script_str, _ = allocate_tokens(
            tokenizer, example.proof_script, self.script_tokens
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

    def collate(self, tokenizer: PreTrainedTokenizer, example: LmExample) -> str:
        input_str = self.collate_input(tokenizer, example)
        out_str, _ = allocate_tokens(
            tokenizer, example.next_steps[0], self.out_tokens, truncate_front=False
        )
        combined_str = input_str + out_str
        return combined_str

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> PremiseCollator:
        return cls(
            yaml_data["script_tokens"],
            yaml_data["state_tokens"],
            yaml_data["premise_tokens"],
            yaml_data["out_tokens"],
        )


@dataclass
class ProofCollator:
    ALIAS = "proof"
    script_tokens: int
    state_tokens: int
    proof_tokens: int
    out_tokens: int

    STATE_SEP = "\n[STATE]\n"
    SCRIPT_SEP = "\n[SCRIPT]\n"
    PROOF_SEP = "\n[PROOFS]\n"

    def collate_input(self, tokenizer: PreTrainedTokenizer, example: LmExample) -> str:
        proof_str = allocate_and_fmt(tokenizer, example.proofs, self.proof_tokens)
        state_str, _ = allocate_tokens(
            tokenizer, example.proof_state, self.state_tokens
        )
        script_str, _ = allocate_tokens(
            tokenizer, example.proof_script, self.script_tokens
        )
        combined_str = (
            self.PROOF_SEP
            + proof_str
            + self.STATE_SEP
            + state_str
            + self.SCRIPT_SEP
            + script_str
            + NEWLINE_RESPONSE_TEMPLATE
        )
        return combined_str

    def collate(self, tokenizer: PreTrainedTokenizer, example: LmExample) -> str:
        input_str = self.collate_input(tokenizer, example)
        out_str, _ = allocate_tokens(
            tokenizer, example.next_steps[0], self.out_tokens, truncate_front=False
        )
        combined_str = input_str + out_str
        return combined_str

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> ProofCollator:
        return cls(
            yaml_data["script_tokens"],
            yaml_data["state_tokens"],
            yaml_data["proof_tokens"],
            yaml_data["out_tokens"],
        )


@dataclass
class ProofPremiseNameCollator:
    ALIAS = "proof-premise-name"
    script_tokens: int
    state_tokens: int
    proof_tokens: int
    premise_tokens: int
    out_tokens: int

    STATE_SEP = "\n[STATE]\n"
    SCRIPT_SEP = "\n[SCRIPT]\n"
    PROOF_SEP = "\n[PROOFS]\n"
    PREMISE_SEP = "\n[PREMISES]\n"
    NAME_MATCH = re.compile(r"\S+\s+(\S+?)[\[\]\{\}\(\):=,\s]")

    def get_proof_str(self, example: LmExample) -> str:
        if example.proofs is None:
            reversed_proofs = []
        else:
            reversed_proofs = example.proofs[::-1]
        return "\n".join(reversed_proofs)

    def get_name(self, premise: str) -> Optional[str]:
        name = self.NAME_MATCH.search(premise)
        if name is None:
            _logger.warning(f"Could not find name in premise: {premise}")
            return None
        (premise_name,) = name.groups()
        return premise_name

    def get_premise_names(self, example: LmExample) -> list[str]:
        if example.premises is None:
            return []
        names: list[str] = []
        for p in example.premises:
            p_name = self.get_name(p)
            if p_name is not None:
                names.append(p_name)
        return names

    def get_premise_str(self, example: LmExample) -> str:
        if example.premises is None:
            reversed_premise_names = []
        else:
            reversed_premises = example.premises[::-1]
            reversed_premise_names: list[str] = []
            for p in reversed_premises:
                p_name = self.get_name(p)
                if p_name is not None:
                    reversed_premise_names.append(p_name)
        return "\n".join(reversed_premise_names)

    def collate_input(self, tokenizer: PreTrainedTokenizer, example: LmExample) -> str:
        proof_str = allocate_and_fmt(tokenizer, example.proofs, self.proof_tokens)
        premise_str = allocate_and_fmt(
            tokenizer, self.get_premise_names(example), self.premise_tokens
        )

        state_str, _ = allocate_tokens(
            tokenizer, example.proof_state, self.state_tokens
        )
        script_str, _ = allocate_tokens(
            tokenizer, example.proof_script, self.script_tokens
        )
        combined_str = (
            self.PREMISE_SEP
            + premise_str
            + self.PROOF_SEP
            + proof_str
            + self.STATE_SEP
            + state_str
            + self.SCRIPT_SEP
            + script_str
            + NEWLINE_RESPONSE_TEMPLATE
        )
        return combined_str

    def collate(self, tokenizer: PreTrainedTokenizer, example: LmExample) -> str:
        out_str, _ = allocate_tokens(
            tokenizer, example.next_steps[0], self.out_tokens, truncate_front=False
        )
        input_str = self.collate_input(tokenizer, example)
        combined_str = input_str + out_str
        return combined_str

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> ProofPremiseNameCollator:
        return cls(
            yaml_data["script_tokens"],
            yaml_data["state_tokens"],
            yaml_data["proof_tokens"],
            yaml_data["premise_tokens"],
            yaml_data["out_tokens"],
        )


@dataclass
class ProofPremiseCollator:
    ALIAS = "proof-premise"
    script_tokens: int
    state_tokens: int
    proof_tokens: int
    premise_tokens: int
    out_tokens: int

    STATE_SEP = "\n[STATE]\n"
    SCRIPT_SEP = "\n[SCRIPT]\n"
    PROOF_SEP = "\n[PROOFS]\n"
    PREMISE_SEP = "\n[PREMISES]\n"

    def collate_input(self, tokenizer: PreTrainedTokenizer, example: LmExample) -> str:
        proof_str = allocate_and_fmt(tokenizer, example.proofs, self.proof_tokens)
        premise_str = allocate_and_fmt(tokenizer, example.premises, self.premise_tokens)
        state_str, _ = allocate_tokens(
            tokenizer, example.proof_state, self.state_tokens
        )
        script_str, _ = allocate_tokens(
            tokenizer, example.proof_script, self.script_tokens
        )
        combined_str = (
            self.PREMISE_SEP
            + premise_str
            + self.PROOF_SEP
            + proof_str
            + self.STATE_SEP
            + state_str
            + self.SCRIPT_SEP
            + script_str
            + NEWLINE_RESPONSE_TEMPLATE
        )
        return combined_str

    def collate(self, tokenizer: PreTrainedTokenizer, example: LmExample) -> str:
        input_str = self.collate_input(tokenizer, example)
        out_str, _ = allocate_tokens(
            tokenizer, example.next_steps[0], self.out_tokens, truncate_front=False
        )
        combined_str = input_str + out_str
        return combined_str

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> ProofPremiseCollator:
        return cls(
            yaml_data["script_tokens"],
            yaml_data["state_tokens"],
            yaml_data["proof_tokens"],
            yaml_data["premise_tokens"],
            yaml_data["out_tokens"],
        )


ExampleCollator = (
    BasicCollator
    | PremiseCollator
    | ProofCollator
    | ProofPremiseCollator
    | ProofPremiseNameCollator
)


def example_collator_from_conf(conf: Any) -> ExampleCollator:
    attempted_alias = conf["alias"]
    match attempted_alias:
        case BasicCollator.ALIAS:
            return BasicCollator.from_yaml(conf)
        case PremiseCollator.ALIAS:
            return PremiseCollator.from_yaml(conf)
        case ProofCollator.ALIAS:
            return ProofCollator.from_yaml(conf)
        case ProofPremiseCollator.ALIAS:
            return ProofPremiseCollator.from_yaml(conf)
        case ProofPremiseNameCollator.ALIAS:
            return ProofPremiseNameCollator.from_yaml(conf)
        case _:
            raise ValueError(f"Could not find example collator: {attempted_alias}")


class LmDataset(Dataset):
    def __init__(
        self,
        data_path: Path,
        tokenizer: PreTrainedTokenizer,
        example_collator: ExampleCollator,
        hard_seq_len: int,
        max_n_examples: Optional[int] = None,
    ) -> None:
        super(LmDataset, self).__init__()
        self.edb = ExampleDB.load(data_path)
        __shuffled_list = list(range(self.edb.size()))
        random.seed(0)
        random.shuffle(__shuffled_list)
        self.edb_map = dict(zip(range(self.edb.size()), __shuffled_list))
        self.raw_examples: list[LmExample] = []
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
        target_lm_example = LmExample.from_json(
            json.loads(self.edb.retrieve(target_idx + 1))
        )
        clean_example = self.example_collator.collate(self.tokenizer, target_lm_example)
        return self.tokenizer(
            clean_example,
            max_length=self.hard_seq_len,
            truncation=True,
            padding="max_length",
        )
