from __future__ import annotations
from typing import Any, Callable, Optional
from pathlib import Path
import yaml
import ipdb
import functools

import sys, os
import re
from enum import Enum

from transformers import (
    AutoTokenizer,
    PreTrainedTokenizer,
    PreTrainedModel,
    BitsAndBytesConfig,
)
import torch

from util.train_utils import get_required_arg

from tactic_gen.lm_example import (
    LmExample,
)
from tactic_gen.train_decoder import (
    TRAINING_CONF_NAME,
    load_config,
    get_tokenizer,
    get_model,
)
from tactic_gen.tactic_data import (
    ExampleCollator,
    ProofPremiseCollator,
    NoScriptCollator,
    example_collator_from_conf,
    example_collator_conf_from_yaml,
    NEWLINE_RESPONSE_TEMPLATE,
)
from model_deployment.model_result import ModelResult, filter_recs


class TokenMask(Enum):
    STATE = 0
    SCRIPT = 1
    PROOF = 2
    PREMISE = 3

    @classmethod
    def from_str(cls, s: str) -> TokenMask:
        match s:
            case "state":
                return cls.STATE
            case "script":
                return cls.SCRIPT
            case "proof":
                return cls.PROOF
            case "premise":
                return cls.PREMISE
            case _:
                raise ValueError(f"Invalid token mask: {s}")


def find_id_start_idx(t: torch.Tensor, s: torch.Tensor) -> Optional[int]:
    for i in range(t.shape[0] - s.shape[0] + 1):
        if torch.all(t[i : i + s.shape[0]] == s):
            return i
    return None


def get_enclosing_seps(
    collator: ExampleCollator, token_mask: TokenMask
) -> tuple[str, str]:
    match collator:
        case ProofPremiseCollator():
            match token_mask:
                case TokenMask.STATE:
                    return (collator.STATE_SEP, collator.SCRIPT_SEP)
                case TokenMask.SCRIPT:
                    return (collator.SCRIPT_SEP, NEWLINE_RESPONSE_TEMPLATE)
                case TokenMask.PROOF:
                    return (collator.PROOF_SEP, collator.STATE_SEP)
                case TokenMask.PREMISE:
                    return (collator.PREMISE_SEP, collator.PROOF_SEP)

        case NoScriptCollator():
            match token_mask:
                case TokenMask.STATE:
                    return (collator.STATE_SEP, NEWLINE_RESPONSE_TEMPLATE)
                case TokenMask.SCRIPT:
                    raise ValueError(
                        "NoScriptCollator does not support SCRIPT token masking."
                    )
                case TokenMask.PROOF:
                    return (collator.PROOF_SEP, collator.STATE_SEP)
                case TokenMask.PREMISE:
                    return (collator.PREMISE_SEP, collator.PROOF_SEP)

        case _:
            raise ValueError(f"Token masking not supported for {collator}.")


def transform_attention_mask(
    collator: ExampleCollator,
    tokenizer: PreTrainedTokenizer,
    token_mask: Optional[TokenMask],
    input_ids: torch.Tensor,
    attn_mask: torch.Tensor,
) -> torch.Tensor:
    if token_mask is None:
        return attn_mask
    start_str, end_str = get_enclosing_seps(collator, token_mask)
    start_ids = tokenizer.encode(start_str, add_special_tokens=False)
    end_ids = tokenizer.encode(end_str, add_special_tokens=False)

    changed_mask = attn_mask.clone()
    for i, id_row in enumerate(input_ids):
        start_idx = find_id_start_idx(id_row, torch.tensor(start_ids))
        end_idx = find_id_start_idx(id_row, torch.tensor(end_ids))
        assert start_idx is not None
        assert end_idx is not None
        changed_mask[i, start_idx:end_idx] = 0
    return changed_mask


class DecoderLocalWrapper:
    ALIAS = "decoder-local"

    def __init__(
        self,
        model: PreTrainedModel,
        tokenizer: PreTrainedTokenizer,
        collator: ExampleCollator,
        hard_seq_len: int,
    ):
        self.model = model
        self.tokenizer = tokenizer
        self.collator = collator
        self.hard_seq_len = hard_seq_len

    def get_recs(
        self,
        example: LmExample,
        n: int,
        current_proof: str,
        beam: bool,
        token_mask_str,
    ) -> ModelResult:
        token_mask = None
        if token_mask_str is not None:
            token_mask = TokenMask.from_str(token_mask_str)
        collated_input = self.collator.collate_input(self.tokenizer, example)
        inputs = self.tokenizer(
            collated_input,
            max_length=self.hard_seq_len,
            truncation=True,
            return_tensors="pt",
        )
        attention_mask = transform_attention_mask(
            self.collator,
            self.tokenizer,
            token_mask,
            inputs["input_ids"],
            inputs["attention_mask"],
        )
        with torch.no_grad():
            outputs = self.model.generate(
                inputs["input_ids"].cuda(),
                max_new_tokens=128,
                return_dict_in_generate=True,
                output_scores=True,
                length_penalty=0,
                num_return_sequences=n,
                temperature=None if beam else 1,
                do_sample=not beam,
                num_beams=n if beam and 1 < n else None,
                attention_mask=attention_mask.cuda(),
            )
        input_num_tokens = inputs["input_ids"].shape[1]
        generated_seqs = outputs.sequences[:, input_num_tokens:]
        tactics = self.tokenizer.batch_decode(generated_seqs, skip_special_tokens=True)
        non_special_tokens = torch.concat(
            [(generated_seqs != t)[:, :, None] for t in self.tokenizer.all_special_ids],
            axis=2,
        ).all(dim=2)
        lengths = non_special_tokens.sum(axis=1).tolist()
        if beam and 1 < n:
            scores = outputs.sequences_scores.tolist()
            return ModelResult(tactics, scores, lengths)
        else:
            with torch.no_grad():
                transition_scores = self.model.compute_transition_scores(
                    generated_seqs, outputs.scores, normalize_logits=True
                )
                scores = (
                    transition_scores.where(
                        transition_scores != -torch.inf, torch.tensor(0.0)
                    )
                    .sum(axis=1)
                    .tolist()
                )
                return ModelResult(tactics, scores, lengths)

    @classmethod
    def get_training_conf(cls, checkpoint_loc: Path) -> Any:
        training_conf_loc = checkpoint_loc.parent / TRAINING_CONF_NAME
        with training_conf_loc.open("r") as f:
            training_conf = yaml.safe_load(f)
        return training_conf

    @classmethod
    def from_checkpoint(cls, checkpoint_loc: Path) -> DecoderLocalWrapper:
        training_conf = cls.get_training_conf(checkpoint_loc)
        hard_seq_length = get_required_arg("hard_seq_len", training_conf)
        example_collator_conf = example_collator_conf_from_yaml(
            training_conf["example_collator"]
        )
        example_collator = example_collator_from_conf(example_collator_conf)
        tokenizer = get_tokenizer(
            get_required_arg("model_name", training_conf), add_eos=False
        )
        model = get_model(str(checkpoint_loc.resolve()))
        return cls(model, tokenizer, example_collator, hard_seq_length)

    @classmethod
    def from_conf(cls, json_data: Any) -> DecoderLocalWrapper:
        name = json_data["checkpoint_loc"]
        return cls.from_checkpoint(Path(name))


class StubWrapper:
    def get_recs(
        self,
        example: LmExample,
        n: int,
        current_proof: str,
        beam: bool,
        token_mask: Optional[str],
    ) -> ModelResult:
        return ModelResult([], [], [])


ModelWrapper = DecoderLocalWrapper | StubWrapper


class WrapperNotFoundError(Exception):
    pass


def wrapper_from_conf(conf: Any) -> ModelWrapper:
    attempted_alias = conf["alias"]
    match attempted_alias:
        case DecoderLocalWrapper.ALIAS:
            return DecoderLocalWrapper.from_conf(conf)
        case _:
            raise WrapperNotFoundError(
                f"Could not find model wrapper: {attempted_alias}"
            )
