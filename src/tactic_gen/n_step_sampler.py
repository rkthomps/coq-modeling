from __future__ import annotations
from typing import Any
from dataclasses import dataclass

from typeguard import typechecked

from data_management.dataset_file import FocusedStep, Goal
from tactic_gen.tactic_pair_encoding import TacticPairEncoding
from tactic_gen.step_parser import normalize, lex, tokens2str
import random


@dataclass
class NStepResult:
    steps: list[FocusedStep]
    resulting_goals: list[Goal]


def get_next_goals(
    sampled_steps: list[FocusedStep], all_steps: list[FocusedStep]
) -> list[Goal]:
    assert len(sampled_steps) <= len(all_steps)
    if len(sampled_steps) == len(all_steps):
        return []
    return all_steps[len(sampled_steps)].goals


class OneStepSampler:
    ALIAS = "one"

    def sample_steps(self, steps: list[FocusedStep]) -> NStepResult:
        assert len(steps) >= 1
        sampled_steps = steps[:1]
        next_goal = get_next_goals(sampled_steps, steps)
        return NStepResult(sampled_steps, next_goal)


@typechecked
class NStepUniformSampler:
    ALIAS = "uniform"

    def __init__(self, samples_per_step: int) -> None:
        self.samples_per_step = samples_per_step

    def sample_steps(self, steps: list[FocusedStep]) -> NStepResult:
        assert len(steps) >= 1
        n_steps = random.randint(1, len(steps))
        sampled_steps = steps[:n_steps]
        next_goal = get_next_goals(sampled_steps, steps)
        return NStepResult(sampled_steps, next_goal)

    def to_json(self) -> Any:
        return {"samples_per_step": self.samples_per_step}

    @classmethod
    def from_json(cls, json_data: Any) -> NStepUniformSampler:
        samples_per_step = json_data["samples_per_step"]
        return cls(samples_per_step)

    @classmethod
    def from_conf(cls, conf: Any) -> NStepUniformSampler:
        return cls.from_json(conf)


@typechecked
class NStepTPESampler:
    ALIAS = "tpe"

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
        assert len(steps) >= 1
        ret_steps: list[FocusedStep] = [steps[0]]
        for step in steps[1:]:
            candidate_steps = ret_steps + [step]
            candidate_strs = self.__get_step_texts(candidate_steps)
            if not self.tpe.contains(candidate_strs):
                break
            ret_steps = candidate_steps
        remaining_goal = get_next_goals(ret_steps, steps)
        return NStepResult(ret_steps, remaining_goal)

    def to_json(self) -> Any:
        return {"tpe": self.tpe.to_json()}

    @classmethod
    def from_json(cls, json_data: Any) -> NStepTPESampler:
        tpe_data = json_data["tpe"]
        tpe = TacticPairEncoding.from_json(tpe_data)
        return cls(tpe)

    @classmethod
    def from_conf(cls, conf: Any) -> NStepTPESampler:
        tpe_loc = conf["tpe_loc"]
        tpe = TacticPairEncoding.load(tpe_loc)
        return cls(tpe)


NStepSampler = OneStepSampler | NStepUniformSampler | NStepTPESampler


class NStepSamplerNotFound(Exception):
    pass


def n_step_to_json(sampler: NStepSampler) -> Any:
    match sampler:
        case OneStepSampler():
            return {"alias": OneStepSampler.ALIAS}
        case NStepUniformSampler():
            return {"alias": NStepUniformSampler.ALIAS} | sampler.to_json()
        case NStepTPESampler():
            return {"alias": NStepTPESampler.ALIAS} | sampler.to_json()


def n_step_from_json(json_data: Any) -> NStepSampler:
    n_step_attempted_alias = json_data["alias"]
    match n_step_attempted_alias:
        case OneStepSampler.ALIAS:
            return OneStepSampler()
        case NStepUniformSampler.ALIAS:
            return NStepUniformSampler.from_json(json_data)
        case NStepTPESampler():
            return NStepTPESampler.from_json(json_data)
        case _:
            raise NStepSamplerNotFound(
                f"Could not find n step sampler with alias: {n_step_attempted_alias}"
            )


def n_step_from_conf(json_data: Any) -> NStepSampler:
    n_step_attempted_alias = json_data["alias"]
    match n_step_attempted_alias:
        case OneStepSampler.ALIAS:
            return OneStepSampler()
        case NStepUniformSampler.ALIAS:
            return NStepUniformSampler.from_conf(json_data)
        case NStepTPESampler():
            return NStepTPESampler.from_conf(json_data)
        case _:
            raise NStepSamplerNotFound(
                f"Could not find n step sampler with alias: {n_step_attempted_alias}"
            )
