from __future__ import annotations
from typing import Any
import math


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
        return {"alias": self.get_alias()}

    @classmethod
    def get_initial_score(cls, branching_factor: int) -> NodeScore:
        raise NotImplementedError

    @classmethod
    def from_unit_score(
        cls, unit_score: float, num_tokens: int, max_branch: int
    ) -> NodeScore:
        raise NotImplementedError

    @classmethod
    def from_json(cls, json_data: Any) -> NodeScore:
        alias = json_data["alias"]
        node_score_type = NODE_SCORE_ALIASES[alias]
        return node_score_type.from_json(json_data)

    @staticmethod
    def get_alias() -> str:
        raise NotImplementedError


class TokenLengthNormalizedScore(NodeScore):
    def __init__(self, sequence_score: int | float, proof_num_tokens: int):
        assert type(sequence_score) == int or type(sequence_score) == float
        assert type(proof_num_tokens) == int
        self.sequence_score = sequence_score
        self.proof_num_tokens = proof_num_tokens

    def compute(self) -> float:
        if self.proof_num_tokens == 0:
            assert self.sequence_score == 0
            return 0
        return self.sequence_score / self.proof_num_tokens

    def agg(self, other: NodeScore) -> NodeScore:
        if not isinstance(other, TokenLengthNormalizedScore):
            raise ValueError(f"Other nodescore must be {self.get_alias()}")
        new_sequence_score = self.sequence_score + other.sequence_score
        new_proof_num_tokens = self.proof_num_tokens + other.proof_num_tokens
        return TokenLengthNormalizedScore(new_sequence_score, new_proof_num_tokens)

    def to_json(self) -> Any:
        parent_json = super(TokenLengthNormalizedScore, self).to_json()
        self_json = {
            "sequence_score": self.sequence_score,
            "proof_num_tokens": self.proof_num_tokens,
        }
        return parent_json | self_json

    @classmethod
    def from_unit_score(
        cls, unit_score: float, num_tokens: int, max_branch: int
    ) -> NodeScore:
        return cls(unit_score, num_tokens)

    @classmethod
    def get_initial_score(cls, branching_factor: int) -> NodeScore:
        score = 0
        num_tokens = 0
        return cls(score, num_tokens)

    @classmethod
    def from_json(cls, json_data: Any) -> TokenLengthNormalizedScore:
        sequence_score = json_data["sequence_score"]
        proof_num_tokens = json_data["proof_num_tokens"]
        return cls(sequence_score, proof_num_tokens)

    @staticmethod
    def get_alias() -> str:
        return "token-normalized-score"


class LastTacGreedyScore(NodeScore):
    def __init__(self, sequence_score: int | float) -> None:
        assert type(sequence_score) == int or type(sequence_score) == float
        self.sequence_score = sequence_score

    def compute(self) -> float:
        return self.sequence_score

    def agg(self, other: NodeScore) -> NodeScore:
        if not isinstance(other, LastTacGreedyScore):
            raise ValueError(f"Other nodescore must be {self.get_alias()}")
        return LastTacGreedyScore(other.sequence_score)

    def to_json(self) -> Any:
        parent_json = super(LastTacGreedyScore, self).to_json()
        self_json = {"sequence_score": self.sequence_score}
        return parent_json | self_json

    @classmethod
    def from_json(cls, json_data: Any) -> LastTacGreedyScore:
        sequence_score = json_data["sequence_score"]
        return cls(sequence_score)

    @classmethod
    def from_unit_score(
        cls, unit_score: float, num_tokens: int, max_branch: int
    ) -> NodeScore:
        return LastTacGreedyScore(unit_score)

    @classmethod
    def get_initial_score(cls, branching_factor: int) -> NodeScore:
        return LastTacGreedyScore(0)

    @staticmethod
    def get_alias() -> str:
        return "last-tac-greedy-score"


class DepthFirstScore(NodeScore):
    def __init__(self, proof_num_tactics: int, sequence_score: int | float) -> None:
        assert type(proof_num_tactics) == int
        assert type(sequence_score) == int or type(sequence_score) == float
        self.proof_num_tactics = proof_num_tactics
        self.sequence_score = sequence_score

    def __ord_key(self) -> tuple[int, int | float]:
        return (self.proof_num_tactics, self.sequence_score)

    def __le__(self, other: DepthFirstScore) -> bool:
        return self.__ord_key() <= other.__ord_key()

    def __lt__(self, other: DepthFirstScore) -> bool:
        return self.__ord_key() < other.__ord_key()

    def compute(self) -> float:
        return self.proof_num_tactics

    def agg(self, other: NodeScore) -> NodeScore:
        if not isinstance(other, DepthFirstScore):
            raise ValueError(f"Other nodescore must be {self.get_alias()}")
        combined_num_tactics = self.proof_num_tactics + other.proof_num_tactics
        combined_sequence_scores = other.sequence_score
        return DepthFirstScore(combined_num_tactics, combined_sequence_scores)

    def to_json(self) -> Any:
        parent_json = super(DepthFirstScore, self).to_json()
        self_json = {
            "proof_num_tactics": self.proof_num_tactics,
            "sequence_score": self.sequence_score,
        }
        return parent_json | self_json

    @classmethod
    def from_json(cls, json_data: Any) -> NodeScore:
        proof_num_tactics = json_data["proof_num_tactics"]
        sequence_score = json_data["sequence_score"]
        return cls(proof_num_tactics, sequence_score)

    @classmethod
    def from_unit_score(
        cls, unit_score: float, num_tokens: int, max_branch: int
    ) -> NodeScore:
        return cls(1, unit_score)

    @classmethod
    def get_initial_score(cls, branching_factor: int) -> NodeScore:
        return cls(0, 0)

    @staticmethod
    def get_alias() -> str:
        return "depth-first-score"


class BreadthFirstScore(NodeScore):
    def __init__(self, proof_num_tactics: int, sequence_score: int | float) -> None:
        assert type(proof_num_tactics) == int
        assert type(sequence_score) == int or type(sequence_score) == float
        self.proof_num_tactics = proof_num_tactics
        self.sequence_score = sequence_score

    def __ord_key(self) -> tuple[int, int | float]:
        return (-1 * self.proof_num_tactics, self.sequence_score)

    def __le__(self, other: BreadthFirstScore) -> bool:
        """We prefer nodes with lower breadth unlike other scores"""
        return self.__ord_key() <= other.__ord_key()

    def __lt__(self, other: BreadthFirstScore) -> bool:
        return self.__ord_key() < other.__ord_key()

    def compute(self) -> float:
        return self.proof_num_tactics

    def agg(self, other: NodeScore) -> NodeScore:
        if not isinstance(other, BreadthFirstScore):
            raise ValueError(f"Other nodescore must be {self.get_alias()}")
        combined_num_tactics = self.proof_num_tactics + other.proof_num_tactics
        combined_sequence_scores = other.sequence_score
        return BreadthFirstScore(combined_num_tactics, combined_sequence_scores)

    def to_json(self) -> Any:
        parent_json = super(BreadthFirstScore, self).to_json()
        self_json = {
            "proof_num_tactics": self.proof_num_tactics,
            "sequence_score": self.sequence_score,
        }
        return parent_json | self_json

    @classmethod
    def from_json(cls, json_data: Any) -> NodeScore:
        proof_num_tactics = json_data["proof_num_tactics"]
        sequence_score = json_data["sequence_score"]
        return cls(proof_num_tactics, sequence_score)

    @classmethod
    def from_unit_score(
        cls, unit_score: float, num_tokens: int, max_branch: int
    ) -> NodeScore:
        return cls(1, unit_score)

    @classmethod
    def get_initial_score(cls, branching_factor: int) -> NodeScore:
        return cls(0, 0)

    @staticmethod
    def get_alias() -> str:
        return "breadth-first-score"


class BranchNormalizedScore(NodeScore):
    def __init__(
        self, sequence_score: int | float, proof_num_tactics: int, branching_factor: int
    ) -> None:
        assert type(sequence_score) == float or type(sequence_score) == int
        assert type(proof_num_tactics) == int
        assert type(branching_factor) == int
        self.sequence_score = sequence_score
        self.proof_num_tactics = proof_num_tactics
        self.branching_factor = branching_factor

    def compute(self) -> float:
        return self.sequence_score - (
            self.proof_num_tactics * math.log(1 / self.branching_factor)
        )

    def agg(self, other: NodeScore) -> BranchNormalizedScore:
        if not isinstance(other, BranchNormalizedScore):
            raise ValueError(f"Other nodescore must be {self.get_alias()}")
        new_sequence_score = self.sequence_score + other.sequence_score
        new_proof_num_tactics = self.proof_num_tactics + other.proof_num_tactics
        return BranchNormalizedScore(
            new_sequence_score, new_proof_num_tactics, self.branching_factor
        )

    def to_json(self) -> Any:
        parent_json = super(BranchNormalizedScore, self).to_json()
        self_json = {
            "alias": self.get_alias(),
            "sequence_score": self.sequence_score,
            "proof_num_tactics": self.proof_num_tactics,
            "branching_factor": self.branching_factor,
        }
        return parent_json | self_json

    @classmethod
    def from_json(cls, json_data: Any) -> BranchNormalizedScore:
        sequence_score = json_data["sequence_score"]
        proof_num_tactics = json_data["proof_num_tactics"]
        branching_factor = json_data["branching_factor"]
        return cls(sequence_score, proof_num_tactics, branching_factor)

    @classmethod
    def get_initial_score(cls, branching_factor: int) -> NodeScore:
        seq_score = 0
        num_tactics = 0
        return cls(seq_score, num_tactics, branching_factor)

    @classmethod
    def from_unit_score(
        cls, unit_score: float, num_tokens: int, max_branch: int
    ) -> NodeScore:
        num_tactics = 1
        return cls(unit_score, num_tactics, max_branch)

    @staticmethod
    def get_alias() -> str:
        return "branch-normalized-score"


NODE_SCORE_ALIASES: dict[str, type[NodeScore]] = {
    BranchNormalizedScore.get_alias(): BranchNormalizedScore,
    TokenLengthNormalizedScore.get_alias(): TokenLengthNormalizedScore,
    LastTacGreedyScore.get_alias(): LastTacGreedyScore,
    BreadthFirstScore.get_alias(): BreadthFirstScore,
    DepthFirstScore.get_alias(): DepthFirstScore,
}
