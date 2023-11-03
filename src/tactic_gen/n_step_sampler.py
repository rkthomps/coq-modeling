from __future__ import annotations
from typing import Any, Optional

from data_management.dataset_file import FocusedStep
from tactic_gen.tactic_pair_encoding import TacticPairEncoding
from tactic_gen.step_parser import normalize, lex, tokens2str
import random


class NStepSampler:
    def __init__(self) -> None:
        pass

    def sample_steps(self, steps: list[FocusedStep]) -> list[FocusedStep]:
        raise NotImplementedError

    def to_json(self) -> Any:
        return {"alias": self.get_alias()}

    @classmethod
    def from_json(cls, json_data: Any) -> NStepSampler:
        alias = json_data["alias"]
        return ALIASES[alias].from_json(json_data)

    @staticmethod
    def get_alias() -> str:
        raise NotImplementedError


class NStepUniformSampler(NStepSampler):
    def __init__(self, samples_per_step: int) -> None:
        assert type(samples_per_step) == int
        super(NStepUniformSampler, self).__init__()
        self.samples_per_step = samples_per_step

    def sample_steps(self, steps: list[FocusedStep]) -> list[FocusedStep]:
        assert len(steps) >= 1
        n_steps = random.randint(1, len(steps))
        return steps[:n_steps]

    def to_json(self) -> Any:
        parent_json_repr = super(NStepUniformSampler, self).to_json()
        self_json_repr = {"samples_per_step": self.samples_per_step}
        return parent_json_repr | self_json_repr

    @classmethod
    def from_json(cls, json_data: Any) -> NStepUniformSampler:
        samples_per_step = json_data["samples_per_step"]
        return cls(samples_per_step)

    @staticmethod
    def get_alias() -> str:
        return "uniform"


class NStepTPESampler(NStepSampler):
    def __init__(self, tpe: TacticPairEncoding) -> None:
        self.tpe = tpe

    def __get_step_texts(self, steps: list[FocusedStep]) -> list[str]:
        out_texts: list[str] = []
        for step in steps:
            try:
                norm_step_str = tokens2str(normalize(lex(step.step.text)))
                out_texts.append(norm_step_str)
            except (ValueError, RecursionError):
                print(f"Could not parse: {step.step.text}")
                out_texts.append("<UNPARSABLE>.")
        return out_texts

    def sample_steps(self, steps: list[FocusedStep]) -> list[FocusedStep]:
        ret_steps: list[FocusedStep] = []
        for step in steps:
            candidate_steps = ret_steps + [step]
            candidate_strs = self.__get_step_texts(candidate_steps)
            if not self.tpe.contains(candidate_strs):
                break
            ret_steps = candidate_steps
        return ret_steps

    def to_json(self) -> Any:
        parent_json_repr = super(NStepTPESampler, self).to_json()
        self_json_repr = {"tpe": self.tpe.to_json()}
        return parent_json_repr | self_json_repr

    @classmethod
    def from_json(cls, json_data: Any) -> NStepTPESampler:
        tpe_data = json_data["tpe"]
        tpe = TacticPairEncoding.from_json(tpe_data)
        return cls(tpe)

    @staticmethod
    def get_alias() -> str:
        return "tpe"


ALIASES: dict[str, type[NStepSampler]] = {
    NStepUniformSampler.get_alias(): NStepUniformSampler,
    NStepTPESampler.get_alias(): NStepTPESampler,
}
