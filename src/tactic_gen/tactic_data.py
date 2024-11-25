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

from model_deployment.conf_utils import (
    formatter_conf_to_client_conf,
    start_servers,
    wait_for_servers,
)

from tactic_gen.lm_example import (
    LmExample,
    LmFormatter,
    FormatterConf,
    formatter_conf_from_yaml,
    formatter_from_conf,
)
from util.train_utils import allocate_tokens
from util.util import get_basic_logger
from util.shuffled_idx import ShuffledIndex
from util.constants import DATA_POINTS_NAME

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
    whole_proof: bool

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
        if self.whole_proof:
            target = "".join(example.next_steps)
        else:
            target = example.next_steps[0]
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
            conf.whole_proof,
        )


@dataclass
class PremiseCollatorConf:
    script_tokens: int
    state_tokens: int
    premise_tokens: int
    out_tokens: int
    whole_proof: bool
    ALIAS = "premise"

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> PremiseCollatorConf:
        return cls(
            yaml_data["script_tokens"],
            yaml_data["state_tokens"],
            yaml_data["premise_tokens"],
            yaml_data["out_tokens"],
            yaml_data.get("whole_proof", False),
        )


@dataclass
class PremiseCollator:
    script_tokens: int
    state_tokens: int
    premise_tokens: int
    out_tokens: int
    whole_proof: bool

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
        if self.whole_proof:
            target = "".join(example.next_steps)
        else:
            target = example.next_steps[0]
        out_str, _ = allocate_tokens(
            tokenizer, target, self.out_tokens, truncate_front=False
        )
        combined_str = input_str + out_str
        return combined_str

    @classmethod
    def from_conf(cls, conf: PremiseCollatorConf) -> PremiseCollator:
        return cls(
            conf.script_tokens,
            conf.state_tokens,
            conf.premise_tokens,
            conf.out_tokens,
            conf.whole_proof,
        )


@dataclass
class ProofCollatorConf:
    script_tokens: int
    state_tokens: int
    proof_tokens: int
    out_tokens: int
    whole_proof: bool
    ALIAS = "proof"

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> ProofCollatorConf:
        return cls(
            yaml_data["script_tokens"],
            yaml_data["state_tokens"],
            yaml_data["proof_tokens"],
            yaml_data["out_tokens"],
            yaml_data.get("whole_proof", False),
        )


@dataclass
class ProofCollator:
    script_tokens: int
    state_tokens: int
    proof_tokens: int
    out_tokens: int
    whole_proof: bool

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
        if self.whole_proof:
            target = "".join(example.next_steps)
        else:
            target = example.next_steps[0]
        out_str, _ = allocate_tokens(
            tokenizer, target, self.out_tokens, truncate_front=False
        )
        combined_str = input_str + out_str
        return combined_str

    @classmethod
    def from_conf(cls, conf: ProofCollatorConf) -> ProofCollator:
        return cls(
            conf.script_tokens,
            conf.state_tokens,
            conf.proof_tokens,
            conf.out_tokens,
            conf.whole_proof,
        )


@dataclass
class ProofPremiseCollatorConf:
    script_tokens: int
    state_tokens: int
    proof_tokens: int
    premise_tokens: int
    out_tokens: int
    whole_proof: bool
    ALIAS = "proof-premise"

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> ProofPremiseCollatorConf:
        return cls(
            yaml_data["script_tokens"],
            yaml_data["state_tokens"],
            yaml_data["proof_tokens"],
            yaml_data["premise_tokens"],
            yaml_data["out_tokens"],
            yaml_data.get("whole_proof", False),
        )


@dataclass
class ProofPremiseCollator:
    script_tokens: int
    state_tokens: int
    proof_tokens: int
    premise_tokens: int
    out_tokens: int
    whole_proof: bool

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
        if self.whole_proof:
            target = "".join(example.next_steps)
        else:
            target = example.next_steps[0]
        out_str, _ = allocate_tokens(
            tokenizer, target, self.out_tokens, truncate_front=False
        )
        combined_str = input_str + out_str
        return combined_str

    @classmethod
    def from_conf(cls, conf: ProofPremiseCollatorConf) -> ProofPremiseCollator:
        return cls(
            conf.script_tokens,
            conf.state_tokens,
            conf.proof_tokens,
            conf.premise_tokens,
            conf.out_tokens,
            conf.whole_proof,
        )


@dataclass
class NoScriptCollatorConf:
    state_tokens: int
    proof_tokens: int
    premise_tokens: int
    out_tokens: int
    whole_proof: bool
    ALIAS = "no-script"

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> NoScriptCollatorConf:
        return cls(
            yaml_data["state_tokens"],
            yaml_data["proof_tokens"],
            yaml_data["premise_tokens"],
            yaml_data["out_tokens"],
            yaml_data.get("whole_proof", False),
        )


@dataclass
class NoScriptCollator:
    state_tokens: int
    proof_tokens: int
    premise_tokens: int
    out_tokens: int
    whole_proof: bool

    STATE_SEP = "\n[STATE]\n"
    PROOF_SEP = "\n[PROOFS]\n"
    PREMISE_SEP = "\n[PREMISES]\n"

    def collate_input(self, tokenizer: PreTrainedTokenizer, example: LmExample) -> str:
        proof_str = allocate_and_fmt(tokenizer, example.proofs, self.proof_tokens)
        premise_str = allocate_and_fmt(tokenizer, example.premises, self.premise_tokens)
        state_str, _ = allocate_tokens(
            tokenizer, example.proof_state, self.state_tokens
        )
        combined_str = (
            self.PREMISE_SEP
            + premise_str
            + self.PROOF_SEP
            + proof_str
            + self.STATE_SEP
            + state_str
            + NEWLINE_RESPONSE_TEMPLATE
        )
        return combined_str

    def collate(self, tokenizer: PreTrainedTokenizer, example: LmExample) -> str:
        input_str = self.collate_input(tokenizer, example)
        if self.whole_proof:
            target = "".join(example.next_steps)
        else:
            target = example.next_steps[0]
        out_str, _ = allocate_tokens(
            tokenizer, target, self.out_tokens, truncate_front=False
        )
        combined_str = input_str + out_str
        return combined_str

    @classmethod
    def from_conf(cls, conf: NoScriptCollatorConf) -> NoScriptCollator:
        return cls(
            conf.state_tokens,
            conf.proof_tokens,
            conf.premise_tokens,
            conf.out_tokens,
            conf.whole_proof,
        )


@functools.lru_cache(maxsize=10000)
def get_file_lines(file: Path) -> list[str]:
    with file.open("r") as f:
        return f.read().split("\n")


@dataclass
class NPrevLineCollatorConf:
    script_tokens: int
    state_tokens: int
    prefix_tokens: int
    out_tokens: int
    data_loc: Path
    line_dict_loc: Path
    whole_proof: bool
    ALIAS = "n-prev-line"

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> NPrevLineCollatorConf:
        return cls(
            yaml_data["script_tokens"],
            yaml_data["state_tokens"],
            yaml_data["prefix_tokens"],
            yaml_data["out_tokens"],
            Path(yaml_data["data_loc"]),
            Path(yaml_data["line_dict_loc"]),
            yaml_data.get("whole_proof", False),
        )


@dataclass
class NPrevLineCollator:
    script_tokens: int
    state_tokens: int
    prefix_tokens: int
    out_tokens: int
    data_loc: Path
    line_dict: LineDict
    whole_proof: bool

    STATE_SEP = "\n[STATE]\n"
    SCRIPT_SEP = "\n[SCRIPT]\n"
    PREFIX_SEP = "\n[PREFIX]\n"

    def get_prefix_lines(self, file_repos_path: Path, proof_idx: int) -> list[str]:
        file_loc = self.data_loc / file_repos_path
        file_lines = get_file_lines(file_loc)

        if self.line_dict.has_file(str(file_repos_path)):
            prefix_lines = file_lines[
                : self.line_dict.get(str(file_repos_path), proof_idx)
            ]
        else:
            prefix_lines = []
        return prefix_lines

    def collate_input(self, tokenizer: PreTrainedTokenizer, example: LmExample) -> str:
        assert example.file_name is not None
        assert example.proof_idx is not None
        prefix_lines = self.get_prefix_lines(
            Path(example.file_name), example.proof_idx
        )[
            ::-1
        ]  # Take last lines
        prefix_str = allocate_and_fmt(tokenizer, prefix_lines, self.prefix_tokens)
        state_str, _ = allocate_tokens(
            tokenizer, example.proof_state, self.state_tokens
        )
        script_str, _ = allocate_tokens(
            tokenizer, example.proof_script, self.script_tokens
        )
        combined_str = (
            self.PREFIX_SEP
            + prefix_str
            + self.STATE_SEP
            + state_str
            + self.SCRIPT_SEP
            + script_str
            + NEWLINE_RESPONSE_TEMPLATE
        )
        return combined_str

    def collate(self, tokenizer: PreTrainedTokenizer, example: LmExample) -> str:
        input_str = self.collate_input(tokenizer, example)
        if self.whole_proof:
            target = "".join(example.next_steps)
        else:
            target = example.next_steps[0]
        out_str, _ = allocate_tokens(
            tokenizer, target, self.out_tokens, truncate_front=False
        )
        combined_str = input_str + out_str
        return combined_str

    @classmethod
    def from_conf(cls, conf: NPrevLineCollatorConf) -> NPrevLineCollator:
        line_dict = LineDict.load(conf.line_dict_loc)
        return cls(
            conf.script_tokens,
            conf.state_tokens,
            conf.prefix_tokens,
            conf.out_tokens,
            conf.data_loc,
            line_dict,
            conf.whole_proof,
        )


ExampleCollator = (
    BasicCollator
    | PremiseCollator
    | ProofCollator
    | ProofPremiseCollator
    | NPrevLineCollator
    | NoScriptCollator
)

ExampleCollatorConf = (
    BasicCollatorConf
    | PremiseCollatorConf
    | ProofCollatorConf
    | ProofPremiseCollatorConf
    | NPrevLineCollatorConf
    | NoScriptCollatorConf
)


def example_collator_conf_from_yaml(yaml_data: Any) -> ExampleCollatorConf:
    attempted_alias = yaml_data["alias"]
    match attempted_alias:
        case BasicCollatorConf.ALIAS:
            return BasicCollatorConf.from_yaml(yaml_data)
        case PremiseCollatorConf.ALIAS:
            return PremiseCollatorConf.from_yaml(yaml_data)
        case ProofCollatorConf.ALIAS:
            return ProofCollatorConf.from_yaml(yaml_data)
        case ProofPremiseCollatorConf.ALIAS:
            return ProofPremiseCollatorConf.from_yaml(yaml_data)
        case NPrevLineCollatorConf.ALIAS:
            return NPrevLineCollatorConf.from_yaml(yaml_data)
        case NoScriptCollatorConf.ALIAS:
            return NoScriptCollatorConf.from_yaml(yaml_data)
        case _:
            raise ValueError(f"Could not find example collator: {attempted_alias}")


def example_collator_from_conf(conf: ExampleCollatorConf) -> ExampleCollator:
    match conf:
        case BasicCollatorConf():
            return BasicCollator.from_conf(conf)
        case PremiseCollatorConf():
            return PremiseCollator.from_conf(conf)
        case ProofCollatorConf():
            return ProofCollator.from_conf(conf)
        case ProofPremiseCollatorConf():
            return ProofPremiseCollator.from_conf(conf)
        case NPrevLineCollatorConf():
            return NPrevLineCollator.from_conf(conf)
        case NoScriptCollatorConf():
            return NoScriptCollator.from_conf(conf)


class LmProcessedDataset(Dataset):
    def __init__(
        self,
        data_path: Path,
        tokenizer: PreTrainedTokenizer,
        example_collator: ExampleCollator,
        hard_seq_len: int,
        max_n_examples: Optional[int] = None,
    ) -> None:
        super(LmProcessedDataset, self).__init__()
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


@dataclass
class TacticDataConf:
    data_loc: Path
    sentence_db_loc: Path
    shuffled_index_loc: Path
    formatter_conf: FormatterConf
    model_name: str
    collator_conf: ExampleCollatorConf
    cache_loc: Path
    hard_seq_len: int
    max_n_examples: Optional[int]

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> TacticDataConf:
        return cls(
            Path(yaml_data["data_loc"]),
            Path(yaml_data["sentence_db_loc"]),
            Path(yaml_data["shuffled_index_loc"]),
            formatter_conf_from_yaml(yaml_data["formatter_conf"]),
            yaml_data["model_name"],
            example_collator_conf_from_yaml(yaml_data["collator_conf"]),
            Path(yaml_data["cache_loc"]),
            yaml_data["hard_seq_len"],
            yaml_data.get("max_n_examples", None),
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


class ExamplePage:
    def __init__(self, dp_name: str, page: dict[int, dict[int, LmExample]]):
        self.dp_name = dp_name
        self.page = page


class ExampleCache:
    def __init__(self, cache_loc: Path):
        self.cache_loc = cache_loc
        os.makedirs(self.cache_loc, exist_ok=True)
        self.num_cached = 0

    def get(
        self,
        step_id: StepID,
        formatter: LmFormatter,
        data_loc: Path,
        sentence_db: SentenceDB,
    ) -> Optional[LmExample]:
        file_loc = self.cache_loc / step_id.file
        if file_loc.exists():
            with file_loc.open("rb") as f:
                page: ExamplePage = pickle.load(f)
                if (
                    step_id.proof_idx in page.page
                    and step_id.step_idx in page.page[step_id.proof_idx]
                ):
                    return page.page[step_id.proof_idx][step_id.step_idx]
                else:
                    return None
        else:
            dp_loc = data_loc / DATA_POINTS_NAME / step_id.file
            dp = DatasetFile.load(dp_loc, sentence_db)
            num_examples = 0
            new_page_dict: dict[int, dict[int, LmExample]] = {}
            for proof_idx, proof in enumerate(dp.proofs):
                new_page_dict[proof_idx] = {}
                for step_idx, step in enumerate(proof.steps):
                    example = formatter.example_from_step(
                        step_idx, proof_idx, dp, training=True
                    )
                    new_page_dict[proof_idx][step_idx] = example
                    num_examples += 1
            new_page = ExamplePage(step_id.file, new_page_dict)
            self.num_cached += num_examples
            with file_loc.open("wb") as f:
                pickle.dump(new_page, f)
            if (
                step_id.proof_idx in new_page_dict
                and step_id.step_idx in new_page_dict[step_id.proof_idx]
            ):
                return new_page_dict[step_id.proof_idx][step_id.step_idx]
            else:
                return None


class LmDataset(Dataset):
    def __init__(
        self,
        data_loc: Path,
        sentence_db: SentenceDB,
        shuffled_idx: ShuffledIndex,
        split: Split,
        formatter: LmFormatter,
        tokenizer: PreTrainedTokenizer,
        example_collator: ExampleCollator,
        cache_loc: Path,
        hard_seq_len: int,
        max_n_examples: Optional[int],
    ) -> None:
        super(LmDataset, self).__init__()
        self.data_loc = data_loc
        self.sentence_db = sentence_db
        self.shuffled_idx = shuffled_idx
        self.split = split
        self.formatter = formatter
        self.tokenizer = tokenizer
        self.example_collator = example_collator
        self.hard_seq_len = hard_seq_len
        self.max_n_examples = max_n_examples
        self.collator = DataCollatorForCompletionOnlyLM(
            response_template=NEWLINE_RESPONSE_TEMPLATE,
            tokenizer=tokenizer,
            mlm=False,
        )
        self.example_cache = ExampleCache(cache_loc)

    def __len__(self) -> int:
        if self.max_n_examples is not None:
            return self.max_n_examples
        return self.shuffled_idx.split_length(self.split)

    def __getitem__(self, index: int) -> Any:
        step_id = self.shuffled_idx.get_idx(self.split, index)
        get_cached = self.example_cache.get(
            step_id, self.formatter, self.data_loc, self.sentence_db
        )
        if get_cached is not None:
            example = get_cached
        else:
            dp = DatasetFile.load(
                self.data_loc / DATA_POINTS_NAME / step_id.file, self.sentence_db
            )
            example = self.formatter.example_from_step(
                step_id.step_idx, step_id.proof_idx, dp, training=True
            )

        clean_example = self.example_collator.collate(self.tokenizer, example)
        return self.tokenizer(
            clean_example,
            max_length=self.hard_seq_len,
            truncation=True,
            padding="max_length",
        )

    @classmethod
    def from_conf(
        cls, conf: TacticDataConf, split: Split, max_num_examples: Optional[int] = None
    ) -> LmDataset:
        formatter_client_conf, next_num, commands = formatter_conf_to_client_conf(
            conf.formatter_conf, 0
        )
        if 0 < len(commands):
            start_servers(commands)
            wait_for_servers(next_num)
        formatter = formatter_from_conf(formatter_client_conf)
        shuffled_idx = ShuffledIndex.load(conf.shuffled_index_loc)
        sentence_db = SentenceDB.load(conf.sentence_db_loc)
        return cls(
            conf.data_loc,
            sentence_db,
            shuffled_idx,
            split,
            formatter,
            get_tokenizer(conf.model_name),
            example_collator_from_conf(conf.collator_conf),
            conf.cache_loc,
            conf.hard_seq_len,
            max_num_examples,
        )
