from __future__ import annotations
from typing import Any

from data_management.dataset_file import DatasetFile, Proof
from tactic_gen.step_parser import lex, normalize, tokens2str


class ProofSelectionExample:
    def __init__(
        self, candidate_proof: str, current_context: str, norm_steps: list[str]
    ) -> None:
        self.candidate_proof = candidate_proof
        self.current_context = current_context
        self.norm_steps = norm_steps

    def to_json(self) -> Any:
        return {
            "candidate_proof": self.candidate_proof,
            "current_context": self.current_context,
            "steps": self.norm_steps,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> ProofSelectionExample:
        candidate_proof = json_data["candidate_proof"]
        current_context = json_data["current_context"]
        steps = json_data["steps"]
        return cls(candidate_proof, current_context, steps)


class BasicCandidateFormatter:
    ALIAS = "basic-candidate"

    def __init__(self) -> None:
        pass

    def format(self, proof: Proof, dp_obj: DatasetFile) -> str:
        goal = proof.theorem.term.text
        norm_steps = [tokens2str(normalize(lex(s.step.text))) for s in proof.steps]
        norm_step_str = "".join(norm_steps)
        return f"{goal}{norm_step_str}"


CandidateFormatter = BasicCandidateFormatter


class BasicContextFormatter:
    ALIAS = "basic-context"

    def __init__(self) -> None:
        pass

    def format(self, proof: Proof, dp_obj: DatasetFile) -> str:
        goal = proof.theorem.term.text
        return goal


ContextFormatter = BasicContextFormatter


class CandidateFormatNotFoundError(Exception):
    pass


class ContextFormatNotFoundError(Exception):
    pass


def context_formatter_from_conf(conf: Any) -> ContextFormatter:
    attempted_alias = conf["alias"]
    match attempted_alias:
        case BasicContextFormatter.ALIAS:
            return BasicContextFormatter()
        case _:
            raise ContextFormatNotFoundError(
                f"Could not find format: {attempted_alias}"
            )


def candidate_formatter_from_conf(conf: Any) -> CandidateFormatter:
    attempted_alias = conf["alias"]
    match attempted_alias:
        case BasicCandidateFormatter.ALIAS:
            return BasicCandidateFormatter()
        case _:
            raise CandidateFormatNotFoundError(
                f"Could not find format: {attempted_alias}"
            )
