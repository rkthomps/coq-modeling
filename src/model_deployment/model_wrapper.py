from __future__ import annotations
from typing import Any, Callable, Optional
import ipdb
import functools

import sys, os
import requests
import json
import yaml
import math

from typeguard import typechecked
from transformers import (
    LlamaForCausalLM,
    T5Tokenizer,
    CodeLlamaTokenizer,
    BitsAndBytesConfig,
)
import torch
import openai

from util.train_utils import get_required_arg

from tactic_gen.lm_example import (
    LmExample,
    THM_SEP,
)
from tactic_gen.train_codellama import (
    TRAINING_CONF_NAME,
    load_config,
    get_tokenizer,
)
from tactic_gen.codellama_data import collate_example
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
        tokenizer: T5Tokenizer,
        local_dset: FidDataset,
    ) -> None:
        self.model = model
        self.tokenizer = tokenizer
        self.local_dset = local_dset

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

    def get_recs(self, example: LmExample, n: int, current_proof: str) -> ModelResult:
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
        tactics = [f"\n{t}" for t in raw_tactics]
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
        tokenizer = T5Tokenizer.from_pretrained(model_name)
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


class CodeLLamaLocalWrapper:
    ALIAS = "local"

    def __init__(
        self,
        model: LlamaForCausalLM,
        tokenizer: CodeLlamaTokenizer,
        stop_strings: list[str],
        collate_fn: Callable[[str], str],
        batch_size: int = 2,
    ) -> None:
        self.model = model
        self.tokenizer = tokenizer
        self.stop_strings = stop_strings
        self.collate_fn = collate_fn
        self.batch_size = batch_size

    # TODO test built in huggingface beam decoding
    def get_recs(self, example: LmExample, n: int, current_proof: str) -> ModelResult:
        collated_input = self.collate_fn(example.input)
        input_ids = self.tokenizer(collated_input, return_tensors="pt")["input_ids"].to(
            "cuda"
        )

        beam_width = n
        n_recs = n
        sample_result = do_beam_sample(
            input_ids,
            self.model,
            self.tokenizer,
            beam_width,
            n_recs,
            self.stop_strings,
            batch_size=self.batch_size,
        )
        # sample_result = self.do_sample(input_ids, n)
        return filter_recs(
            sample_result.tactics,
            sample_result.scores,
            sample_result.num_tokens,
            self.stop_strings,
        )

    def to_device(self, device: str) -> None:
        self.model.to(device)

    @staticmethod
    def get_model_loc(checkpoint_loc: str) -> str:
        return os.path.dirname(checkpoint_loc)

    @classmethod
    def from_checkpoint(cls, checkpoint_loc: str) -> CodeLLamaLocalWrapper:
        model_loc = cls.get_model_loc(checkpoint_loc)
        model_conf = load_config(os.path.join(model_loc, TRAINING_CONF_NAME))
        quant_conf = BitsAndBytesConfig(
            load_in_4bit=True, bnb_4bit_compute_dtype=torch.float16
        )

        model = LlamaForCausalLM.from_pretrained(
            checkpoint_loc,
            quantization_config=quant_conf,
        )
        tokenizer = get_tokenizer(model_conf)
        tokenizer.add_eos_token = False
        max_input_len = model_conf["max_input_len"]
        max_seq_len = model_conf["max_seq_len"]

        def collate_fn(input_s: str) -> str:
            output_s = ""
            collated_in, _ = collate_example(
                tokenizer,
                max_input_len,
                max_seq_len,
                input_s,
                output_s,
            )
            return collated_in

        return cls(model, tokenizer, collate_fn)

    @classmethod
    def from_conf(cls, json_data: Any) -> ModelWrapper:
        name = json_data["checkpoint_loc"]
        return cls.from_checkpoint(name)


class StubWrapper:
    def get_recs(self, example: LmExample, n: int, current_proof: str) -> ModelResult:
        return ModelResult([], [], [])


ModelWrapper = CodeLLamaLocalWrapper | FidT5LocalWrapper | StubWrapper


class WrapperNotFoundError(Exception):
    pass


def wrapper_from_conf(conf: Any) -> ModelWrapper:
    attempted_alias = conf["alias"]
    match attempted_alias:
        case CodeLLamaLocalWrapper.ALIAS:
            return CodeLLamaLocalWrapper.from_conf(conf)
        case FidT5LocalWrapper.ALIAS:
            return FidT5LocalWrapper.from_conf(conf)
        case _:
            raise WrapperNotFoundError(
                f"Could not find model wrapper: {attempted_alias}"
            )
