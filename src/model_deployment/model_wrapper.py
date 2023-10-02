from __future__ import annotations
from typing import Any
import pdb

import sys, os
import requests
import json
import math

from tactic_gen.lm_example import LmExample, GPT4BasicLmExample
from model_deployment.node_score import NodeScore, CodeLLamaNodeScore

import openai

class ModelResult:
    def __init__(self, 
                 next_tactic_list: list[str], 
                 score_list: list[NodeScore]) -> None:
        assert all([type(t) == str for t in next_tactic_list])
        assert all([isinstance(s, NodeScore) for s in score_list]) 
        assert len(next_tactic_list) == len(score_list)
        self.next_tactic_list = next_tactic_list
        self.score_list = score_list


class ModelWrapper:
    def get_recs(self, example: LmExample, n: int) -> ModelResult:
        raise NotImplementedError

    @classmethod
    def from_json(cls, json_data: Any) -> ModelWrapper:
        raise NotImplementedError

    @staticmethod
    def get_alias() -> str:
        raise NotImplementedError


class CodeLLamaServer(ModelWrapper):
    """Finetuned version of codellama"""
    def __init__(self, server_url: str) -> None:
        assert type(server_url) == str
        self.server_url = server_url

    def __filter_recs(self, next_tactics: list[str],
                    next_scores: list[CodeLLamaNodeScore]) -> ModelResult:
        scores_and_tactics = list(zip(next_scores, next_tactics))
        scores_and_tactics.sort(reverse=True)
        final_tactics: list[str] = []
        final_scores: list[NodeScore] = []
        seen_tactics: set[str] = set()
        for score, tactic in scores_and_tactics:
            stripped_tactic = tactic.strip()
            if stripped_tactic in seen_tactics:
                continue
            seen_tactics.add(stripped_tactic)
            final_tactics.append(tactic)
            final_scores.append(score)
        return ModelResult(final_tactics, final_scores)


    def get_recs(self, example: LmExample, n: int) -> ModelResult:
        request_data = example.to_json()
        request_data["n"] = "n"
        response = requests.post(self.server_url, request_data)
        response_data = json.loads(response.content)
        next_tactic_list = response_data["tactics"]
        score_list = response_data["scores"]
        num_tokens_list = response_data["num_tokens"] 
        assert len(score_list) == len(num_tokens_list)
        llama_scores: list[CodeLLamaNodeScore] = []
        for score, toks in zip(score_list, num_tokens_list):
            llama_scores.append(CodeLLamaNodeScore(score, toks))
        return self.__filter_recs(next_tactic_list, llama_scores)

    @classmethod
    def from_json(cls, json_data: Any) -> ModelWrapper:
        server_url = json_data["server_url"]
        return cls(server_url) 

    @staticmethod
    def get_alias() -> str:
        return "codellama-server"


class GPT4Wrapper(ModelWrapper):
    ENV_API_KEY_NAME = "OPENAI_API_KEY"
    ENV_ORG_KEY_NAME = "OPENAI_ORG_KEY"
    MODEL = "gpt-4"
    def __init__(self) -> None:
        if os.environ[self.ENV_API_KEY_NAME] is None:
            raise ValueError(("Must set environment variable"
                              f"'{self.ENV_API_KEY_NAME}' to your api key"))
        self.api_key = os.environ.get(self.ENV_API_KEY_NAME)
        self.org_key = os.environ.get(self.ENV_ORG_KEY_NAME)

    def __filter_recs(self, completion: Any) -> ModelResult:
        assert type(completion) == dict
        seen_tactics: set[str] = set()
        tactics: list[str] = []
        scores: list[NodeScore] = []
        for choice in completion["choices"]:
            assert type(choice) == dict
            assert type(choice["message"]) == dict
            raw_msg = choice["message"]["content"]
            assert type(raw_msg) == str
            stripped_msg = raw_msg.strip()
            if stripped_msg in seen_tactics:
                continue 
            seen_tactics.add(stripped_msg)
            assert type(choice["logprobs"]) == dict
            token_logprobs = completion["logprobs"]["top_logprobs"]
            assert type(token_logprobs) == dict
            logprobs_alone = [v for k, v in token_logprobs.items()]
            sequence_score = sum(logprobs_alone)
            num_logprobs = len(logprobs_alone)
            tactics.append(raw_msg)
            scores.append(CodeLLamaNodeScore(sequence_score, num_logprobs))
        return ModelResult(tactics, scores)

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
        scores: list[NodeScore] = []
        sorted_tactics = sorted(tactic_freqs.items(), 
                                key=lambda tup: -1 * tup[1])
        for tactic, freq in sorted_tactics[:n]: 
            tactics.append(raw_tactic_map[tactic])
            psuedo_num_tokens = len(tactic.split())
            scores.append(
                CodeLLamaNodeScore(math.log(freq / sum_responses), psuedo_num_tokens))
        return ModelResult(tactics, scores)


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
            #logprobs=1,
        )
        return self.__filter_recs_no_logprobs(completion, n) 


    @staticmethod
    def get_alias() -> str:
        return "gpt4"


MODEL_WRAPPER_ALIASES: dict[str, type[ModelWrapper]] = {
    CodeLLamaServer.get_alias(): CodeLLamaServer,
    GPT4Wrapper.get_alias(): GPT4Wrapper,
}


        





