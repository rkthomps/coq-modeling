from __future__ import annotations
from typing import Any, Callable, Optional
import pdb
import functools

import sys, os
import requests
import json
import math

from transformers import (
    LlamaForCausalLM,
    CodeLlamaTokenizer,
    BitsAndBytesConfig,
    StoppingCriteriaList,
)
from transformers.generation.utils import SampleDecoderOnlyOutput
import torch


from data_management.create_lm_dataset import LmExampleConfig, DATA_CONF_NAME
from model_deployment.premise_model_wrapper import LocalPremiseModelWrapper
from tactic_gen.lm_example import (
    LmExample,
    GPT4BasicLmExample,
    BaseCodeLLamaLmExample,
    BaseCodeLLamaPremiseLmExample,
)
from tactic_gen.train_codellama import (
    TRAINING_CONF_NAME,
    load_config,
    get_tokenizer,
    collate_input,
)
from model_deployment.node_score import NodeScore, BranchNormalizedScore
from model_deployment.codellama_utils import (
    SampleResult,
    PeriodStoppingCriteria,
    get_sequence_score,
    do_beam_sample,
)

import openai


class ModelResult:
    def __init__(
        self,
        next_tactic_list: list[str],
        score_list: list[float],
        num_tokens_list: list[int],
    ) -> None:
        assert all([type(t) == str for t in next_tactic_list])
        assert all([type(s) == float for s in score_list])
        assert all([type(t) == int for t in num_tokens_list])
        assert len(next_tactic_list) == len(score_list)
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


class ModelWrapper:
    def __init__(self, lm_example_config: LmExampleConfig) -> None:
        assert type(lm_example_config) == LmExampleConfig
        self.lm_example_config = lm_example_config

    def get_recs(self, example: LmExample, n: int) -> ModelResult:
        raise NotImplementedError

    @classmethod
    def from_json(cls, json_data: Any) -> ModelWrapper:
        raise NotImplementedError

    @staticmethod
    def get_alias() -> str:
        raise NotImplementedError


class CodeLLamaLocalWrapper(ModelWrapper):
    def __init__(
        self,
        model: LlamaForCausalLM,
        tokenizer: CodeLlamaTokenizer,
        lm_example_conf: LmExampleConfig,
        collate_fn: Callable[[str], str],
        batch_size: int = 2,
    ) -> None:
        super(CodeLLamaLocalWrapper, self).__init__(lm_example_conf)
        assert type(model) == LlamaForCausalLM
        assert type(tokenizer) == CodeLlamaTokenizer
        self.model = model
        self.tokenizer = tokenizer
        self.stopping_criteria = PeriodStoppingCriteria.from_tokenizer(self.tokenizer)
        self.collate_fn = collate_fn
        self.batch_size = batch_size

    @staticmethod
    def __clean_tactic(tactic: str) -> str:
        while "\n\n" in tactic:
            tactic = tactic.replace("\n\n", "\n")
        return tactic

    @classmethod
    def __filter_recs(
        cls,
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
            final_tactics.append(cls.__clean_tactic(tactic))
            final_scores.append(score)
            final_num_tokens.append(num_tokens)
        return ModelResult(final_tactics, final_scores, final_num_tokens)

    def do_sample(
        self, input_ids: torch.LongTensor, n: int, temperature: float = 0.2
    ) -> SampleResult:
        self.stopping_criteria.set_num_periods(input_ids)
        stopping_list = StoppingCriteriaList([self.stopping_criteria])
        tactics: list[str] = []
        scores: list[float] = []
        num_tokens: list[int] = []
        for i in range(n):
            output = self.model.generate(
                input_ids,
                temperature=temperature,
                do_sample=True,
                max_new_tokens=32,
                output_scores=True,
                return_dict_in_generate=True,
                stopping_criteria=stopping_list,
            )
            assert type(output) == SampleDecoderOnlyOutput
            output_sequence = output.sequences[0]
            input_sequence = input_ids[0]
            output_length = len(output.scores)
            tactic = self.tokenizer.decode(
                output_sequence[len(input_sequence) :], skip_special_tokens=True
            )
            score = get_sequence_score(
                input_sequence, output_sequence, output.scores, self.stopping_criteria
            )
            tactics.append(tactic)
            scores.append(score)
            num_tokens.append(output_length)
        return SampleResult(tactics, scores, num_tokens)

    def get_recs(self, example: LmExample, n: int) -> ModelResult:
        collated_input = self.collate_fn(example.input)
        input_ids = self.tokenizer(collated_input, return_tensors="pt")["input_ids"].to(
            "cuda"
        )
        model_input = self.tokenizer.decode(input_ids[0])
        print(model_input)

        beam_width = n
        n_recs = n
        sample_result = do_beam_sample(
            input_ids,
            self.model,
            self.tokenizer,
            beam_width,
            n_recs,
            self.stopping_criteria,
            batch_size=self.batch_size,
        )
        print(sample_result.tactics)
        # sample_result = self.do_sample(input_ids, n)
        return self.__filter_recs(
            sample_result.tactics, sample_result.scores, sample_result.num_tokens
        )

    @staticmethod
    def get_model_loc(checkpoint_loc: str) -> str:
        return os.path.dirname(checkpoint_loc)

    @classmethod
    def from_name(
        cls, model_name: str, premise_wrapper: Optional[LocalPremiseModelWrapper] = None
    ) -> CodeLLamaLocalWrapper:
        quant_conf = BitsAndBytesConfig(
            load_in_4bit=True, bnb_4bit_compute_dtype=torch.float16
        )
        model = LlamaForCausalLM.from_pretrained(
            model_name,
            quantization_config=quant_conf,
        )
        tokenizer = CodeLlamaTokenizer.from_pretrained(model_name)
        if premise_wrapper:
            lm_example_conf = LmExampleConfig.from_example_type_and_premise_wrapper(
                BaseCodeLLamaPremiseLmExample, premise_wrapper
            )
        else:
            lm_example_conf = LmExampleConfig.from_example_type_and_premise_wrapper(
                BaseCodeLLamaLmExample, None
            )
        max_input_len = 448
        collate_fn = lambda x: collate_input(
            tokenizer, max_input_len, x, response_template=""
        )
        return cls(model, tokenizer, lm_example_conf, collate_fn)

    @classmethod
    def from_checkpoint(cls, checkpoint_loc: str) -> CodeLLamaLocalWrapper:
        model_loc = cls.get_model_loc(checkpoint_loc)
        model_conf = load_config(os.path.join(model_loc, TRAINING_CONF_NAME))
        quant_conf = BitsAndBytesConfig(
            load_in_4bit=True, bnb_4bit_compute_dtype=torch.float16
        )
        lm_example_conf = LmExampleConfig.load(os.path.join(model_loc, DATA_CONF_NAME))
        model = LlamaForCausalLM.from_pretrained(
            checkpoint_loc,
            quantization_config=quant_conf,
        )
        tokenizer = get_tokenizer(model_conf)
        tokenizer.add_eos_token = False
        max_input_len = model_conf["max_input_len"]
        collate_fn = lambda x: collate_input(tokenizer, max_input_len, x)
        return cls(model, tokenizer, lm_example_conf, collate_fn)

    @classmethod
    def from_pretrained(
        cls,
        name_or_checkpoint: str,
        premise_wrapper: Optional[LocalPremiseModelWrapper] = None,
    ) -> CodeLLamaLocalWrapper:
        if os.path.exists(name_or_checkpoint):
            return cls.from_checkpoint(name_or_checkpoint)
        else:
            return cls.from_name(name_or_checkpoint, premise_wrapper)

    @classmethod
    def from_json(cls, json_data: Any) -> ModelWrapper:
        name = json_data["pretrained-name"]
        if "premise-model" in json_data:
            premise_checkpoint_loc = json_data["premise-model"]
            premise_wrapper = LocalPremiseModelWrapper.from_checkpoint(
                premise_checkpoint_loc
            )
        else:
            premise_wrapper = None
        return cls.from_pretrained(name, premise_wrapper)

    @staticmethod
    def get_alias() -> str:
        return "codellama-local"


FORMAT_NAME = "/format"
INFERENCE_NAME = "/codellama"


class CodeLLamaServer(ModelWrapper):
    """Finetuned version of codellama"""

    def __init__(self, server_url: str, lm_example_conf: LmExampleConfig) -> None:
        super(CodeLLamaServer, self).__init__(lm_example_conf)
        assert type(server_url) == str
        self.server_url = server_url.rstrip("/") + INFERENCE_NAME

    def get_recs(self, example: LmExample, n: int) -> ModelResult:
        request_data = example.to_json()
        request_data["n"] = str(n)
        response = requests.post(self.server_url, request_data)
        response_data = json.loads(response.content)
        response_obj = ModelResult.from_json(response_data)
        return response_obj

    @classmethod
    def from_json(cls, json_data: Any) -> ModelWrapper:
        server_url = json_data["server_url"]
        assert type(server_url) == str
        stripped_url = server_url.rstrip("/")
        format_endpoint = stripped_url + FORMAT_NAME
        format_response = requests.post(format_endpoint, {})
        format_data = json.loads(format_response.content)
        format_config = LmExampleConfig.from_json(format_data)
        return cls(server_url, format_config)

    @classmethod
    def from_url(cls, url: str) -> ModelWrapper:
        return cls.from_json({"server_url": url})

    @staticmethod
    def get_alias() -> str:
        return "codellama_server"


class GPT4Wrapper(ModelWrapper):
    ENV_API_KEY_NAME = "OPENAI_API_KEY"
    ENV_ORG_KEY_NAME = "OPENAI_ORG_KEY"
    MODEL = "gpt-4"

    def __init__(self) -> None:
        gpt_lm_conf = LmExampleConfig.from_example_type_and_premise_wrapper(
            GPT4BasicLmExample, None
        )
        super(GPT4Wrapper, self).__init__(gpt_lm_conf)
        if os.environ[self.ENV_API_KEY_NAME] is None:
            raise ValueError(
                (
                    "Must set environment variable"
                    f"'{self.ENV_API_KEY_NAME}' to your api key"
                )
            )
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
        assert type(example) == GPT4BasicLmExample

        messages = [
            {"role": "system", "content": GPT4BasicLmExample.SYS_MSG},
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

    @staticmethod
    def get_alias() -> str:
        return "gpt4"


MODEL_WRAPPER_ALIASES: dict[str, type[ModelWrapper]] = {
    CodeLLamaServer.get_alias(): CodeLLamaServer,
    CodeLLamaLocalWrapper.get_alias(): CodeLLamaLocalWrapper,
    GPT4Wrapper.get_alias(): GPT4Wrapper,
}
