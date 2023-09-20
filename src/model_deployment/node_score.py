from __future__ import annotations
from typing import Type

class NodeScore:
    def __init__(self) -> None:
        pass

    def __le__(self, other: NodeScore) -> bool:
        return self.compute() <= other.compute()

    def __lt__(self, other: NodeScore) -> bool:
        return self.compute() < other.compute()

    def agg(self, other: NodeScore) -> NodeScore:
        raise NotImplementedError

    def compute(self) -> float:
        raise NotImplementedError

    @classmethod
    def get_initial_score(cls) -> NodeScore:
        raise NotImplementedError

    @staticmethod
    def get_alias() -> str:
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

    @staticmethod
    def get_alias() -> str:
        return "codellama-node-score"


NODE_SCORE_ALIASES: dict[str, Type[NodeScore]] = {
    CodeLLamaNodeScore.get_alias(): CodeLLamaNodeScore,
}