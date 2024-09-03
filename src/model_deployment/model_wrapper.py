from __future__ import annotations
from typing import Any, Callable, Optional
from pathlib import Path
import yaml
import ipdb
import functools

import sys, os
import re

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
    example_collator_from_conf,
    example_collator_conf_from_yaml,
)
from model_deployment.model_result import ModelResult, filter_recs


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
        self, example: LmExample, n: int, current_proof: str, beam: bool
    ) -> ModelResult:
        collated_input = self.collator.collate_input(self.tokenizer, example)
        with open("out.txt", "a") as fout:
            fout.write(collated_input)
        # print("Collated: ", collated_input)
        inputs = self.tokenizer(
            collated_input,
            max_length=self.hard_seq_len,
            truncation=True,
            return_tensors="pt",
        )
        with torch.no_grad():
            outputs = self.model.generate(
                inputs["input_ids"],
                max_new_tokens=128,
                return_dict_in_generate=True,
                output_scores=True,
                length_penalty=0,
                num_return_sequences=n,
                temperature=None if beam else 1,
                do_sample=not beam,
                num_beams=n if beam and 1 < n else None,
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
        self, example: LmExample, n: int, current_proof: str, beam: bool = False
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
