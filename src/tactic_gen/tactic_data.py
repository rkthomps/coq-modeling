from __future__ import annotations

import re
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


@dataclass
class BasicCollator:
    state_tokens: int
    script_tokens: int
    out_tokens: int

    ALIAS = "basic"
    STATE_SEP = "\n[STATE]\n"
    SCRIPT_SEP = "\n[SCRIPT]\n"

    def collate(self, tokenizer: PreTrainedTokenizer, example: LmExample) -> str:
        state_str, _ = allocate_tokens(
            tokenizer, example.proof_state, self.state_tokens
        )
        script_str, _ = allocate_tokens(
            tokenizer, example.proof_script, self.script_tokens
        )
        out_str, _ = allocate_tokens(
            tokenizer, example.next_steps[0], self.out_tokens, truncate_front=False
        )
        combined_str = (
            self.STATE_SEP
            + state_str
            + self.SCRIPT_SEP
            + script_str
            + NEWLINE_RESPONSE_TEMPLATE
            + out_str
        )
        return combined_str

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> BasicCollator:
        return cls(
            yaml_data["state_tokens"],
            yaml_data["script_tokens"],
            yaml_data["out_tokens"],
        )


class PremiseCollator:
    ALIAS = "premise"
    script_tokens: int
    state_tokens: int
    premise_tokens: int
    out_tokens: int

    def collate(self, tokenizer: PreTrainedTokenizer, example: LmExample) -> str:
        pass

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> PremiseCollator:
        pass


class ProofCollator:
    ALIAS = "proof"
    script_tokens: int
    state_tokens: int
    proof_tokens: int
    out_tokens: int

    def collate(self, tokenizer: PreTrainedTokenizer, example: LmExample) -> str:
        pass

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> ProofCollator:
        pass


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

    def collate(self, tokenizer: PreTrainedTokenizer, example: LmExample) -> str:
        all_premises_names_str = self.get_premise_str(example)
        all_proofs_str = self.get_proof_str(example)
        premise_str, _ = allocate_tokens(
            tokenizer, all_premises_names_str, self.premise_tokens
        )
        proof_str, _ = allocate_tokens(tokenizer, all_proofs_str, self.proof_tokens)
        state_str, _ = allocate_tokens(
            tokenizer, example.proof_state, self.state_tokens
        )
        script_str, _ = allocate_tokens(
            tokenizer, example.proof_script, self.script_tokens
        )
        out_str, _ = allocate_tokens(
            tokenizer, example.next_steps[0], self.out_tokens, truncate_front=False
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
            + out_str
        )
        return combined_str

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> ProofPremiseNameCollator:
        return cls(
            yaml_data["state_tokens"],
            yaml_data["script_tokens"],
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

    def get_proof_str(self, example: LmExample) -> str:
        if example.proofs is None:
            reversed_proofs = []
        else:
            reversed_proofs = example.proofs[::-1]
        return "\n".join(reversed_proofs)

    def get_premise_str(self, example: LmExample) -> str:
        if example.premises is None:
            reversed_premises = []
        else:
            reversed_premises = example.premises[::-1]
        return "\n".join(reversed_premises)

    def collate(self, tokenizer: PreTrainedTokenizer, example: LmExample) -> str:
        all_premises_str = self.get_premise_str(example)
        all_proofs_str = self.get_proof_str(example)
        premise_str, _ = allocate_tokens(
            tokenizer, all_premises_str, self.premise_tokens
        )
        proof_str, _ = allocate_tokens(tokenizer, all_proofs_str, self.proof_tokens)
        state_str, _ = allocate_tokens(
            tokenizer, example.proof_state, self.state_tokens
        )
        script_str, _ = allocate_tokens(
            tokenizer, example.proof_script, self.script_tokens
        )
        out_str, _ = allocate_tokens(
            tokenizer, example.next_steps[0], self.out_tokens, truncate_front=False
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
            + out_str
        )
        return combined_str

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> ProofPremiseCollator:
        return cls(
            yaml_data["state_tokens"],
            yaml_data["script_tokens"],
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
        # case PremiseCollator.ALIAS:
        #     pass
        # case ProofCollator.ALIAS:
        #     pass
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
        self.edb = ExampleDB.load(data_path)
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
        target_lm_example = LmExample.from_json(json.loads(self.edb.retrieve(idx + 1)))
        clean_example = self.example_collator.collate(self.tokenizer, target_lm_example)
        return self.tokenizer(
            clean_example,
            max_length=self.hard_seq_len,
            truncation=True,
            padding="max_length",
        )
