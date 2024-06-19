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
from tactic_gen.tactic_data import ExampleCollator, example_collator_from_conf
from tactic_gen.fid_model import FiDT5
from tactic_gen.fid_data import FidDataset
from model_deployment.codellama_utils import (
    do_beam_sample,
)
from model_deployment.model_result import ModelResult, filter_recs


class FidT5LocalWrapper:
    ALIAS = "fid-local"

    def __init__(
        self,
        model: FiDT5,
        tokenizer: AutoTokenizer,
        local_dset: FidDataset,
    ) -> None:
        self.model = model
        self.tokenizer = tokenizer
        self.local_dset = local_dset

    def __add_whitespace(self, tactic: str) -> str:
        whitespace_pattern = r"\s"
        whitespace_match = re.match(whitespace_pattern, tactic)
        if whitespace_match is None:
            return "\n" + tactic
        return tactic

    def get_current_proof_words(self, current_proof: str) -> list[str]:
        return current_proof.split()

    def get_sequence_biases(self, current_proof: str) -> dict[tuple[int], float]:
        current_words = current_proof.split()
        bias_inc = 0.1
        word_biases: dict[str, float] = {}
        for w in current_words:
            sp_w = " " + w
            if sp_w not in word_biases:
                word_biases[sp_w] = 0.0
            word_biases[sp_w] -= bias_inc

        seq_biases: dict[tuple[int, float]] = {}
        for w, b in word_biases.items():
            w_seq = tuple(self.tokenizer([w], add_special_tokens=False).input_ids[0])
            seq_biases[w_seq] = b
        if len(seq_biases) == 0:
            seq_biases = {(0,): 0.0}
        return seq_biases

    def get_recs(
        self, example: LmExample, n: int, current_proof: str, beam: bool
    ) -> ModelResult:
        seq_bias = self.get_sequence_biases(current_proof)
        # print(seq_bias)
        input_batch = self.local_dset.collate([example])
        with torch.no_grad():
            # TODO THIS BREAKS with n=1
            if n == 1:
                outputs = self.model.generate(
                    input_batch["input_ids"].cuda(),
                    input_batch["attention_mask"].cuda(),
                    64,
                    return_dict_in_generate=True,
                    output_scores=True,
                )
                scores = [1]
            else:
                outputs = self.model.generate(
                    input_batch["input_ids"].cuda(),
                    input_batch["attention_mask"].cuda(),
                    64,
                    # do_sample=True,
                    # temperature=0.6,
                    # encoder_repetition_penalty=0.5,
                    # sequence_bias=seq_bias,
                    return_dict_in_generate=True,
                    output_scores=True,
                    num_beams=n,
                    length_penalty=0,
                    num_return_sequences=n,
                )
                scores = outputs.sequences_scores.tolist()

        raw_tactics = self.tokenizer.batch_decode(
            outputs.sequences, skip_special_tokens=True
        )
        tactics = [f"{self.__add_whitespace(t)}" for t in raw_tactics]
        not_pad_or_eos = ~(
            (outputs.sequences == self.tokenizer.pad_token_id)
            + (outputs.sequences == self.tokenizer.eos_token_id)
        )
        num_tokens = torch.where(not_pad_or_eos, 1, 0).sum(axis=1).tolist()
        return filter_recs(tactics, scores, num_tokens, [])

    @staticmethod
    def get_model_loc(checkpoint_loc: str) -> str:
        return os.path.dirname(checkpoint_loc)

    @classmethod
    def from_checkpoint(cls, checkpoint_loc: str) -> FidT5LocalWrapper:
        model_loc = cls.get_model_loc(checkpoint_loc)
        model_conf = load_config(os.path.join(model_loc, TRAINING_CONF_NAME))
        model = FiDT5.from_pretrained(checkpoint_loc)
        model.cuda()
        model_name = model_conf["model_name"]
        tokenizer = AutoTokenizer.from_pretrained(model_name)
        max_encode_len = get_required_arg("max_encode_len", model_conf)
        max_decode_len = get_required_arg("max_decode_len", model_conf)
        max_num_passages = get_required_arg("max_num_passages", model_conf)
        local_dset = FidDataset(
            None, tokenizer, max_encode_len, max_decode_len, max_num_passages
        )
        return cls(model, tokenizer, local_dset)

    @classmethod
    def from_conf(cls, json_data: Any) -> ModelWrapper:
        name = json_data["checkpoint_loc"]
        return cls.from_checkpoint(name)


class DecoderLocalWrapper:
    ALIAS = "decoder-local"

    def __init__(
        self,
        model: PreTrainedModel,
        tokenizer: PreTrainedTokenizer,
        collator: ExampleCollator,
    ):
        self.model = model
        self.tokenizer = tokenizer
        self.collator = collator

    def get_beam_recs(
        self, example: LmExample, n: int, current_proof: str
    ) -> ModelResult:
        collated_input = self.collator.collate_input(self.tokenizer, example)
        print("Collated: ", collated_input)
        inputs = self.tokenizer(collated_input, return_tensors="pt")
        with torch.no_grad():
            if n == 1:
                outputs = self.model.generate(
                    inputs["input_ids"],
                    max_new_tokens=128,
                    return_dict_in_generate=True,
                    output_scores=True,
                )
                scores = [1]
            else:
                outputs = self.model.generate(
                    inputs["input_ids"],
                    max_new_tokens=128,
                    return_dict_in_generate=True,
                    output_scores=True,
                    num_beams=n,
                    length_penalty=0,
                    num_return_sequences=n,
                )
                scores = outputs.sequences_scores.tolist()
        input_num_tokens = inputs["input_ids"].shape[1]
        tactics = self.tokenizer.batch_decode(
            outputs.sequences[:, input_num_tokens:], skip_special_tokens=True
        )
        not_pad_or_eos = ~(
            (outputs.sequences == self.tokenizer.pad_token_id)
            + (outputs.sequences == self.tokenizer.eos_token_id)
        )
        num_tokens = torch.where(not_pad_or_eos, 1, 0).sum(axis=1).tolist()
        return filter_recs(tactics, scores, num_tokens, [])

    def get_rand_recs(
        self, example: LmExample, n: int, current_proof: str
    ) -> ModelResult:
        collated_input = self.collator.collate_input(self.tokenizer, example)
        print("Collated: ", collated_input)
        inputs = self.tokenizer(collated_input, return_tensors="pt")
        with torch.no_grad():
            out = self.model.generate(
                inputs["input_ids"],
                max_new_tokens=self.collator.out_tokens,
                do_sample=True,
                num_return_sequences=n,
                temperature=1,
            )
        input_num_tokens = inputs["input_ids"].shape[1]
        tactics = self.tokenizer.batch_decode(
            out[:, input_num_tokens:], skip_special_tokens=True
        )
        scores = [1.0] * len(tactics)
        tokenized_out = self.tokenizer(tactics)["input_ids"]
        lengths = [len(t) for t in tokenized_out]
        return ModelResult(tactics, scores, lengths)

    def get_recs(
        self, example: LmExample, n: int, current_proof: str, beam: bool
    ) -> ModelResult:
        if beam:
            return self.get_beam_recs(example, n, current_proof)
        else:
            return self.get_rand_recs(example, n, current_proof)

    @classmethod
    def get_training_conf(cls, checkpoint_loc: Path) -> Any:
        training_conf_loc = checkpoint_loc.parent / TRAINING_CONF_NAME
        with training_conf_loc.open("r") as f:
            training_conf = yaml.safe_load(f)
        return training_conf

    @classmethod
    def from_checkpoint(cls, checkpoint_loc: Path) -> DecoderLocalWrapper:
        training_conf = cls.get_training_conf(checkpoint_loc)
        example_collator_conf = training_conf["example_collator"]
        example_collator = example_collator_from_conf(example_collator_conf)
        tokenizer = get_tokenizer(training_conf, add_eos=False)
        model = get_model(str(checkpoint_loc.resolve()))
        return cls(model, tokenizer, example_collator)

    @classmethod
    def from_conf(cls, json_data: Any) -> DecoderLocalWrapper:
        name = json_data["checkpoint_loc"]
        return cls.from_checkpoint(Path(name))


class StubWrapper:
    def get_recs(self, example: LmExample, n: int, current_proof: str) -> ModelResult:
        return ModelResult([], [], [])


ModelWrapper = DecoderLocalWrapper | FidT5LocalWrapper | StubWrapper


class WrapperNotFoundError(Exception):
    pass


def wrapper_from_conf(conf: Any) -> ModelWrapper:
    attempted_alias = conf["alias"]
    match attempted_alias:
        case DecoderLocalWrapper.ALIAS:
            return DecoderLocalWrapper.from_conf(conf)
        case FidT5LocalWrapper.ALIAS:
            return FidT5LocalWrapper.from_conf(conf)
        case _:
            raise WrapperNotFoundError(
                f"Could not find model wrapper: {attempted_alias}"
            )
