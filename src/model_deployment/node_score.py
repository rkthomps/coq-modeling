from __future__ import annotations
from typing import Type, Any, Union

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

    def to_json(self) -> Any:
        raise NotImplementedError

    @classmethod
    def get_initial_score(cls) -> NodeScore:
        raise NotImplementedError

    @classmethod
    def from_json(cls, json_data: Any) -> NodeScore:
        alias = json_data["alias"]
        node_score_type = NODE_SCORE_ALIASES[alias]
        return node_score_type.from_json(json_data)
        raise NotImplementedError

    @staticmethod
    def get_alias() -> str:
        raise NotImplementedError


class CodeLLamaNodeScore(NodeScore):
    def __init__(self, sequence_score: Union[int, float], 
                 sequence_num_tokens: int) -> None:
        assert (type(sequence_score) == float or
                type(sequence_score) == int)
        assert type(sequence_num_tokens) == int
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

    def to_json(self) -> Any:
        return {
            "sequence_score": self.sequence_score,
            "sequence_num_tokens": self.sequence_num_tokens,
        }
    
    @classmethod
    def from_json(cls, json_data: Any) -> CodeLLamaNodeScore:
        sequence_score = json_data["sequence_score"] 
        sequence_num_toks = json_data["sequence_num_tokens"]
        return cls(sequence_score, sequence_num_toks) 


    @classmethod
    def get_initial_score(cls) -> CodeLLamaNodeScore:
        return cls(0, 0)

    @staticmethod
    def get_alias() -> str:
        return "codellama-node-score"


NODE_SCORE_ALIASES: dict[str, Type[NodeScore]] = {
    CodeLLamaNodeScore.get_alias(): CodeLLamaNodeScore,
}