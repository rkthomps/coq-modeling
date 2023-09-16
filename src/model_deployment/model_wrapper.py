from __future__ import annotations

import requests
import json

from data_management.lm_example import LmExample


class NodeScore:
    
    def __init__(self) -> None:
        pass

    def __le__(self, other: NodeScore) -> bool:
        return self.compute() <= other.compute()

    def agg(self, other: NodeScore) -> NodeScore:
        raise NotImplementedError

    def compute(self) -> float:
        raise NotImplementedError

    @classmethod
    def get_initial_score(cls) -> NodeScore:
        raise NotImplementedError


class CodeLLamaNodeScore(NodeScore):
    def __init__(self, sequence_score: float, 
                 sequence_num_tokens: int) -> None:
        self.sequence_score = sequence_score
        self.sequence_num_tokens = sequence_num_tokens

    def compute(self) -> float:
        if self.sequence_num_tokens == 0:
            assert self.sequence_score == 0
            return 0
        return self.sequence_score / self.sequence_num_tokens

    def agg(self, other: NodeScore) -> CodeLLamaNodeScore:
        if not isinstance(other, CodeLLamaNodeScore):
            raise ValueError("Other nodescore must be codellamanodescore")
        new_sequence_score = self.sequence_score + other.sequence_score
        new_seq_len = self.sequence_num_tokens + other.sequence_num_tokens
        return CodeLLamaNodeScore(new_sequence_score, new_seq_len)

    @classmethod
    def get_initial_score(cls) -> CodeLLamaNodeScore:
        return cls(0, 0)



class ModelResult:
    def __init__(self, 
                 next_tactic_list: list[str], 
                 score_list: [list[NodeScore]]) -> None:
        assert all([type(t) == str for t in next_tactic_list])
        assert all([type(s) == float for s in score_list]) 
        assert len(next_tactic_list) == len(score_list)
        self.next_tactic_list = next_tactic_list
        self.score_list = score_list


class ModelWrapper:
    def get_recs(self, example: LmExample, n: int) -> ModelResult:
        raise NotImplementedError


class CodeLLamaServer(ModelWrapper):
    def __init__(self, server_url: str) -> None:
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
        request_data["n": n]
        response = requests.post(self.server_url, example.to_json())
        response_data = json.loads(response.content)
        next_tactic_list = response_data["tactics"]
        score_list = response_data["scores"]
        num_tokens_list = response_data["num_tokens"] 
        assert len(score_list) == len(num_tokens_list)
        llama_scores: list[CodeLLamaNodeScore] = []
        for score, toks in zip(score_list, num_tokens_list):
            llama_scores.append(CodeLLamaNodeScore(score, toks))
        return self.__filter_recs(next_tactic_list, llama_scores)
        





