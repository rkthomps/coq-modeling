from __future__ import annotations
from typing import Any
from dataclasses import dataclass

from data_management.dataset_file import FocusedStep, Goal
from tactic_gen.tactic_pair_encoding import TacticPairEncoding
from tactic_gen.step_parser import normalize, lex, tokens2str
import random


@dataclass
class NStepResult:
    steps: list[FocusedStep]
    resulting_goals: list[Goal]


def __get_next_goals(
    sampled_steps: list[FocusedStep], all_steps: list[FocusedStep]
) -> list[Goal]:
    assert len(sampled_steps) <= len(all_steps)
    if len(sampled_steps) == len(all_steps):
        return []
    return all_steps[len(sampled_steps)].goals


class NStepSampler:
    def __init__(self) -> None:
        pass

    def sample_steps(self, steps: list[FocusedStep]) -> NStepResult:
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


class OneStepSampler(NStepSampler):
    def __init__(self) -> None:
        pass

    def sample_steps(self, steps: list[FocusedStep]) -> NStepResult:
        assert len(steps) >= 1
        sampled_steps = steps[:1]
        next_goal = __get_next_goals(sampled_steps, steps)
        return NStepResult(sampled_steps, next_goal)

    def to_json(self) -> Any:
        return super(OneStepSampler, self).to_json()

    @classmethod
    def from_json(cls, json_data: Any) -> OneStepSampler:
        return cls()

    @staticmethod
    def get_alias() -> str:
        return "one"


class NStepUniformSampler(NStepSampler):
    def __init__(self, samples_per_step: int) -> None:
        assert type(samples_per_step) == int
        super(NStepUniformSampler, self).__init__()
        self.samples_per_step = samples_per_step

    def sample_steps(self, steps: list[FocusedStep]) -> NStepResult:
        assert len(steps) >= 1
        n_steps = random.randint(1, len(steps))
        sampled_steps = steps[:n_steps]
        next_goal = __get_next_goals(sampled_steps, steps)
        return NStepResult(sampled_steps, next_goal)

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

    def sample_steps(self, steps: list[FocusedStep]) -> NStepResult:
        ret_steps: list[FocusedStep] = []
        for step in steps:
            candidate_steps = ret_steps + [step]
            candidate_strs = self.__get_step_texts(candidate_steps)
            if not self.tpe.contains(candidate_strs):
                break
            ret_steps = candidate_steps
        remaining_goal = __get_next_goals(ret_steps, steps)
        return NStepResult(ret_steps, remaining_goal)

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
    OneStepSampler.get_alias(): OneStepSampler,
    NStepUniformSampler.get_alias(): NStepUniformSampler,
    NStepTPESampler.get_alias(): NStepTPESampler,
}
