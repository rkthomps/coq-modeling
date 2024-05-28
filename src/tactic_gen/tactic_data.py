from __future__ import annotations

from typing import Any, Optional
from pathlib import Path
import json
from dataclasses import dataclass

from torch.utils.data import Dataset
from transformers import PreTrainedTokenizer, BatchEncoding
from trl import DataCollatorForCompletionOnlyLM
import jsonlines
from typeguard import typechecked
from data_management.jsonl_utils import ExampleDB

from tactic_gen.lm_example import LmExample
from util.train_utils import allocate_tokens

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
        state_str, _ = allocate_tokens(tokenizer, example.proof_state, self.state_tokens)
        script_str, _ = allocate_tokens(tokenizer, example.proof_script, self.script_tokens)
        out_str, _ = allocate_tokens(tokenizer, example.target, self.out_tokens)
        return self.STATE_SEP + state_str  + self.SCRIPT_SEP + script_str + NEWLINE_RESPONSE_TEMPLATE + out_str

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> BasicCollator:
        return cls(yaml_data["state_tokens"], yaml_data["script_tokens"], yaml_data["out_tokens"])


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

class ProofPremiseCollator:
    ALIAS = "proof-premise"
    script_tokens: int
    state_tokens: int
    proof_tokens: int
    premise_tokens: int
    out_tokens: int

    def collate(self, tokenizer: PreTrainedTokenizer, example: LmExample) -> str:
        pass

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> ProofPremiseCollator:
        pass


ExampleCollator = BasicCollator | PremiseCollator | ProofCollator | ProofPremiseCollator

def example_collator_from_conf(conf: Any):
    attempted_alias = conf["alias"]
    match attempted_alias:
        case BasicCollator.ALIAS:
            pass
        case PremiseCollator.ALIAS:
            pass
        case ProofCollator.ALIAS:
            pass
        case ProofPremiseCollator.ALIAS:
            pass
        case _:
            raise ValueError(f"Could not find example collator: {attempted_alias}")


@typechecked
class LmDataset(Dataset):
    def __init__(
        self,
        data_path: Path,
        tokenizer: PreTrainedTokenizer,
        example_collator: ExampleCollator,
        max_n_examples: Optional[int] = None,
    ) -> None:
        self.edb = ExampleDB.load(data_path)
        self.raw_examples: list[LmExample] = []
        self.collator = DataCollatorForCompletionOnlyLM(
            response_template=NEWLINE_RESPONSE_TEMPLATE
            tokenizer=tokenizer, mlm=False,
        )
        self.tokenizer = tokenizer
        self.example_collator = example_collator
        self.max_n_examples = max_n_examples

    def __len__(self) -> int:
        if self.max_n_examples is not None:
            return self.max_n_examples
        return self.edb.size()

    def __getitem__(self, idx: int) -> BatchEncoding:
        target_lm_example = LmExample.from_json(json.loads(self.edb.retrieve(idx + 1)))
        clean_example = self.example_collator.collate(self.tokenizer, target_lm_example)
        return self.tokenizer(
            clean_example
        )
