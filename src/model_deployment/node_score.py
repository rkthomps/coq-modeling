from __future__ import annotations
from typing import Any
import math


class NodeScore:
    def __init__(self, branching_factor: int) -> None:
        assert type(branching_factor) == int
        self.branching_factor = branching_factor

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
    def get_initial_score(cls, branching_factor: int) -> NodeScore:
        raise NotImplementedError

    @classmethod
    def from_unit_score(cls, branching_factor: int, unit_score: float) -> NodeScore:
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
    def __init__(
        self, branching_factor: int, sequence_score: int | float, proof_num_tactics: int
    ) -> None:
        super(CodeLLamaNodeScore, self).__init__(branching_factor)
        assert type(sequence_score) == float or type(sequence_score) == int
        assert type(proof_num_tactics) == int
        self.sequence_score = sequence_score
        self.proof_num_tactics = proof_num_tactics

    def compute(self) -> float:
        return self.sequence_score - (
            self.proof_num_tactics * math.log(1 / self.branching_factor)
        )

    def agg(self, other: NodeScore) -> CodeLLamaNodeScore:
        if not isinstance(other, CodeLLamaNodeScore):
            raise ValueError("Other nodescore must be codellamanodescore")
        new_sequence_score = self.sequence_score + other.sequence_score
        new_proof_num_tactics = self.proof_num_tactics + other.proof_num_tactics
        return CodeLLamaNodeScore(
            self.branching_factor, new_sequence_score, new_proof_num_tactics
        )

    def to_json(self) -> Any:
        return {
            "alias": self.get_alias(),
            "branching_factor": self.branching_factor,
            "sequence_score": self.sequence_score,
            "proof_num_tactics": self.proof_num_tactics,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> CodeLLamaNodeScore:
        branching_factor = json_data["branching_factor"]
        sequence_score = json_data["sequence_score"]
        proof_num_tactics = json_data["proof_num_tactics"]
        return cls(branching_factor, sequence_score, proof_num_tactics)

    @classmethod
    def get_initial_score(cls, branching_factor: int) -> CodeLLamaNodeScore:
        return cls(branching_factor, 0, 0)

    @classmethod
    def from_unit_score(cls, branching_factor: int, unit_score: float) -> NodeScore:
        return cls(branching_factor, unit_score, 1)

    @staticmethod
    def get_alias() -> str:
        return "codellama-node-score"


NODE_SCORE_ALIASES: dict[str, type[NodeScore]] = {
    CodeLLamaNodeScore.get_alias(): CodeLLamaNodeScore,
}
