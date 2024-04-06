from __future__ import annotations
from typing import Any
from dataclasses import dataclass

from data_management.dataset_file import FocusedStep, Goal
from tactic_gen.tactic_pair_encoding import TacticPairEncoding
from tactic_gen.step_parser import normalize, lex, tokens2str, CoqParseError
from util.util import get_basic_logger
import random

_logger = get_basic_logger(__name__)


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
    def sample_steps(self, steps: list[FocusedStep]) -> NStepResult:
        assert len(steps) >= 1
        sampled_steps = steps[:1]
        next_goal = get_next_goals(sampled_steps, steps)
        return NStepResult(sampled_steps, next_goal)


class NStepUniformSampler:
    def __init__(self, samples_per_step: int) -> None:
        self.samples_per_step = samples_per_step

    def sample_steps(self, steps: list[FocusedStep]) -> NStepResult:
        assert len(steps) >= 1
        n_steps = random.randint(1, len(steps))
        sampled_steps = steps[:n_steps]
        next_goal = get_next_goals(sampled_steps, steps)
        return NStepResult(sampled_steps, next_goal)

    @classmethod
    def from_conf(cls, conf: NStepUniformConf) -> NStepUniformSampler:
        return cls(conf.samples_per_step)


class NStepTPESampler:
    def __init__(self, tpe: TacticPairEncoding) -> None:
        self.tpe = tpe

    def __get_step_texts(self, steps: list[FocusedStep]) -> list[str]:
        out_texts: list[str] = []
        for step in steps:
            try:
                norm_step_str = tokens2str(normalize(lex(step.step.text)))
                out_texts.append(norm_step_str)
            except CoqParseError:
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

    @classmethod
    def from_conf(cls, conf: NStepTPEConf) -> NStepTPESampler:
        tpe = TacticPairEncoding.load(conf.tpe_loc)
        return cls(tpe)

@dataclass
class NStepUniformConf:
    ALIAS = "uniform"
    samples_per_step: int

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> NStepUniformConf:
        return cls(yaml_data["uniform"])


@dataclass
class NStepTPEConf:
    ALIAS = "tpe"
    tpe_loc: str

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> NStepTPEConf:
        return cls(yaml_data["tpe_loc"])


class OneStepConf:
    ALIAS = "one"


NStepConf = NStepTPEConf | NStepUniformConf | OneStepConf 

def n_step_conf_from_yaml(yaml_data: Any) -> NStepConf:
    attempted_alias = yaml_data["alias"]
    match attempted_alias:
        case NStepTPEConf.ALIAS:
            return NStepTPEConf.from_yaml(yaml_data)
        case NStepUniformConf.ALIAS:
            return NStepUniformConf.from_yaml(yaml_data)
        case OneStepConf.ALIAS:
            return OneStepConf()
        case _:
            raise ValueError("N step conf not found: " + attempted_alias)


NStepSampler = OneStepSampler | NStepUniformSampler | NStepTPESampler
def n_step_from_conf(conf: NStepConf) -> NStepSampler:
    match conf:
        case NStepTPEConf():
            return NStepTPESampler.from_conf(conf) 
        case NStepUniformConf():
            return NStepUniformSampler.from_conf(conf)
        case OneStepConf(): 
            return OneStepSampler()
