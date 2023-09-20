from __future__ import annotations
from typing import Type, Any

import requests
import json

from data_management.lm_example import LmExample
from model_deployment.node_score import NodeScore, CodeLLamaNodeScore


class ModelResult:
    def __init__(self, 
                 next_tactic_list: list[str], 
                 score_list: [list[NodeScore]]) -> None:
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
        request_data["n"] = n
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

MODEL_WRAPPER_ALIASES: dict[str, ModelWrapper] = {
    CodeLLamaServer.get_alias(): CodeLLamaServer,
}


        





