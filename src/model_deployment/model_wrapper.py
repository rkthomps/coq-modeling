from __future__ import annotations
from typing import Any, Callable, Optional
import pdb
import functools

import sys, os
import requests
import json
import yaml
import math

from typeguard import typechecked
from transformers import (
    LlamaForCausalLM,
    CodeLlamaTokenizer,
    BitsAndBytesConfig,
)
import torch
import openai

from data_management.create_lm_dataset import LmExampleConfig, DATA_CONF_NAME

from tactic_gen.lm_example import (
    LmExample,
    LmFormatter,
    GPT4Formatter,
    fmt_from_conf,
    fmt_get_stop_strings,
)
from tactic_gen.train_codellama import (
    TRAINING_CONF_NAME,
    load_config,
    get_tokenizer,
)
from tactic_gen.codellama_data import collate_example
from model_deployment.codellama_utils import (
    do_beam_sample,
)


@typechecked
class ModelResult:
    def __init__(
        self,
        next_tactic_list: list[str],
        score_list: list[float],
        num_tokens_list: list[int],
    ) -> None:
        self.next_tactic_list = next_tactic_list
        self.score_list = score_list
        self.num_tokens_list = num_tokens_list

    def to_json(self) -> Any:
        return {
            "next_tactic_list": self.next_tactic_list,
            "score_list": self.score_list,
            "num_tokens_list": self.num_tokens_list,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> ModelResult:
        next_tactic_list = json_data["next_tactic_list"]
        score_list = json_data["score_list"]
        num_tokens_list = json_data["num_tokens_list"]
        return cls(next_tactic_list, score_list, num_tokens_list)


@typechecked
class CodeLLamaLocalWrapper:
    ALIAS = "local"

    def __init__(
        self,
        model: LlamaForCausalLM,
        tokenizer: CodeLlamaTokenizer,
        formatter: LmFormatter,
        stop_strings: list[str],
        collate_fn: Callable[[str], str],
        batch_size: int = 2,
    ) -> None:
        self.model = model
        self.tokenizer = tokenizer
        self.formatter = formatter
        self.stop_strings = stop_strings
        self.collate_fn = collate_fn
        self.batch_size = batch_size

    def __remove_stop_strings(self, s: str) -> str:
        for stop_str in self.stop_strings:
            stop_idx = s.find(stop_str)
            if stop_idx > -1:
                return s[:stop_idx]
        return s

    def __filter_recs(
        self,
        next_tactics: list[str],
        next_scores: list[float],
        next_num_tokens: list[int],
    ) -> ModelResult:
        scores_and_tactics = list(zip(next_scores, next_tactics, next_num_tokens))
        scores_and_tactics.sort(reverse=True)
        final_tactics: list[str] = []
        final_scores: list[float] = []
        final_num_tokens: list[int] = []
        seen_tactics: set[str] = set()
        for score, tactic, num_tokens in scores_and_tactics:
            stripped_tactic = tactic.strip()
            if stripped_tactic in seen_tactics:
                continue
            seen_tactics.add(stripped_tactic)
            final_tactics.append(self.__remove_stop_strings(tactic))
            final_scores.append(score)
            final_num_tokens.append(num_tokens)
        return ModelResult(final_tactics, final_scores, final_num_tokens)

    def get_recs(self, example: LmExample, n: int) -> ModelResult:
        collated_input = self.collate_fn(example.input)
        input_ids = self.tokenizer(collated_input, return_tensors="pt")["input_ids"].to(
            "cuda"
        )
        model_input = self.tokenizer.decode(input_ids[0])

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
        return self.__filter_recs(
            sample_result.tactics, sample_result.scores, sample_result.num_tokens
        )

    def to_device(self, device: str) -> None:
        self.model.to(device)

    @staticmethod
    def get_model_loc(checkpoint_loc: str) -> str:
        return os.path.dirname(checkpoint_loc)

    @classmethod
    def from_name(
        cls,
        model_name: str,
        formatter: LmFormatter,
        stop_strings: Optional[list[str]],
    ) -> CodeLLamaLocalWrapper:
        quant_conf = BitsAndBytesConfig(
            load_in_4bit=True, bnb_4bit_compute_dtype=torch.float16
        )
        model = LlamaForCausalLM.from_pretrained(
            model_name,
            quantization_config=quant_conf,
        )
        tokenizer = CodeLlamaTokenizer.from_pretrained(model_name)
        formatter = fmt_from_conf(formatter_conf)

        max_input_len = 448
        max_seq_len = 512

        def collate_fn(input_s: str) -> str:
            output_s = ""
            collated_in, _ = collate_example(
                tokenizer,
                max_input_len,
                max_seq_len,
                input_s,
                output_s,
                response_template="",
            )
            return collated_in

        if not stop_strings:
            stop_strings = ["."]
        return cls(model, tokenizer, formatter, stop_strings, collate_fn)

    @classmethod
    def from_checkpoint(
        cls, checkpoint_loc: str, formatter: Optional[LmFormatter]
    ) -> CodeLLamaLocalWrapper:
        model_loc = cls.get_model_loc(checkpoint_loc)
        model_conf = load_config(os.path.join(model_loc, TRAINING_CONF_NAME))
        quant_conf = BitsAndBytesConfig(
            load_in_4bit=True, bnb_4bit_compute_dtype=torch.float16
        )
        if formatter is None:
            conf_loc = os.path.join(model_loc, DATA_CONF_NAME)
            with open(conf_loc, "r") as fin:
                conf = yaml.load(fin, Loader=yaml.Loader)
            formatter = fmt_from_conf(conf[LmExampleConfig.FORMATTER_KEY])

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

        stop_strings: list[str] = fmt_get_stop_strings(formatter)
        return cls(model, tokenizer, formatter, stop_strings, collate_fn)

    @classmethod
    def from_pretrained(
        cls,
        name_or_checkpoint: str,
        formatter: Optional[LmFormatter],
        stop_strings: Optional[list[str]] = None,
    ) -> CodeLLamaLocalWrapper:
        if os.path.exists(name_or_checkpoint):
            return cls.from_checkpoint(name_or_checkpoint, formatter)
        else:
            if formatter is None:
                raise ValueError(
                    "Must pass a formatter configuration when loading a base model."
                )
            return cls.from_name(name_or_checkpoint, formatter, stop_strings)

    @classmethod
    def from_conf(cls, json_data: Any) -> ModelWrapper:
        name = json_data["pretrained-name"]
        formatter = (
            fmt_from_conf(json_data["formatter"]) if "formatter" in json_data else None
        )
        return cls.from_pretrained(name, formatter)


FORMAT_NAME = "/format"
INFERENCE_NAME = "/codellama"


@typechecked
class CodeLLamaServer:
    """Finetuned version of codellama"""

    ALIAS = "server"

    def __init__(self, server_url: str, formatter: LmFormatter) -> None:
        self.server_url = server_url.rstrip("/") + INFERENCE_NAME
        self.formatter = formatter

    def get_recs(self, example: LmExample, n: int) -> ModelResult:
        request_data = example.to_json()
        request_data["n"] = str(n)
        response = requests.post(self.server_url, request_data)
        response_data = json.loads(response.content)
        response_obj = ModelResult.from_json(response_data)
        return response_obj

    @classmethod
    def from_conf(cls, conf: Any) -> CodeLLamaServer:
        server_url = conf["server_url"]
        assert type(server_url) == str
        stripped_url = server_url.rstrip("/")
        format_endpoint = stripped_url + FORMAT_NAME
        format_response = requests.post(format_endpoint, {})
        format_data = json.loads(format_response.content)
        formatter = fmt_from_conf(format_data)
        return cls(server_url, formatter)


class GPT4Wrapper:
    ENV_API_KEY_NAME = "OPENAI_API_KEY"
    ENV_ORG_KEY_NAME = "OPENAI_ORG_KEY"
    MODEL = "gpt-4"
    ALIAS = "gpt4"

    def __init__(self) -> None:
        self.formatter = GPT4Formatter()
        self.api_key = os.environ.get(self.ENV_API_KEY_NAME)
        self.org_key = os.environ.get(self.ENV_ORG_KEY_NAME)

    def __filter_recs_no_logprobs(self, completion: Any, n: int) -> ModelResult:
        tactic_freqs: dict[str, int] = {}
        raw_tactic_map: dict[str, str] = {}
        for choice in completion["choices"]:
            raw_msg = choice["message"]["content"]
            assert type(raw_msg) == str
            stripped_msg = raw_msg.strip()
            if stripped_msg in tactic_freqs:
                tactic_freqs[stripped_msg] += 1
            else:
                tactic_freqs[stripped_msg] = 1
                raw_tactic_map[stripped_msg] = raw_msg
        sum_responses = len(completion["choices"])
        tactics: list[str] = []
        scores: list[float] = []
        num_tokens: list[int] = []
        sorted_tactics = sorted(tactic_freqs.items(), key=lambda tup: -1 * tup[1])
        for tactic, freq in sorted_tactics[:n]:
            tactics.append(raw_tactic_map[tactic])
            psuedo_num_tokens = len(tactic.split())
            scores.append(math.log(freq / sum_responses))
            num_tokens.append(psuedo_num_tokens)
        return ModelResult(tactics, scores, num_tokens)

    def get_recs(self, example: LmExample, n: int) -> ModelResult:
        messages = [
            {"role": "system", "content": self.formatter.SYS_MSG},
            {"role": "user", "content": example.input},
        ]

        print(messages)
        # Currently logprobs are not supported in the
        # ChatCompletion API. Once they are we should add them.
        completion = openai.ChatCompletion.create(
            model=self.MODEL,
            messages=messages,
            temperature=1,
            n=math.ceil(n * 2),
            # logprobs=1,
        )
        return self.__filter_recs_no_logprobs(completion, n)


ModelWrapper = CodeLLamaLocalWrapper | CodeLLamaServer | GPT4Wrapper


class WrapperNotFoundError(Exception):
    pass


def wrapper_from_conf(conf: Any) -> ModelWrapper:
    attempted_alias = conf["alias"]
    match attempted_alias:
        case CodeLLamaLocalWrapper.ALIAS:
            return CodeLLamaLocalWrapper.from_conf(conf)
        case CodeLLamaServer.ALIAS:
            return CodeLLamaServer.from_conf(conf)
        case GPT4Wrapper.ALIAS:
            return GPT4Wrapper()
        case _:
            raise WrapperNotFoundError(
                f"Could not find model wrapper: {attempted_alias}"
            )


def wrapper_to_device(wrapper: ModelWrapper, device: str) -> None:
    match wrapper:
        case CodeLLamaLocalWrapper():
            wrapper.to_device(device)
        case _:
            pass
