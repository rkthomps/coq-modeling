from __future__ import annotations
from typing import Any

from data_management.dataset_file import FocusedStep
import random


class NStepSampler:
    def __init__(self) -> None:
        pass

    def sample_steps(self, steps: list[FocusedStep]) -> list[list[FocusedStep]]:
        raise NotImplementedError

    def to_json(self) -> Any:
        return {"alias": self.get_alias()}

    @classmethod
    def from_json(cls, json_data: Any) -> NStepUniformSampler:
        alias = json_data["alias"]
        return ALIASES[alias].from_json(json_data)

    @classmethod
    def get_alias(cls) -> str:
        raise NotImplementedError


class NStepUniformSampler(NStepSampler):
    def __init__(self, samples_per_step: int) -> None:
        assert type(samples_per_step) == int
        super(NStepUniformSampler, self).__init__()
        self.samples_per_step = samples_per_step

    def sample_steps(self, steps: list[FocusedStep]) -> list[list[FocusedStep]]:
        assert len(steps) >= 1
        sample_population = list(range(1, len(steps) + 1))
        num_to_sample = min(len(steps), self.samples_per_step)
        stop_indices = random.sample(sample_population, num_to_sample)
        return [steps[:stop] for stop in stop_indices]

    def to_json(self) -> Any:
        parent_json_repr = super(NStepUniformSampler, self).to_json()
        assert "samples_per_step" not in parent_json_repr
        parent_json_repr["samples_per_step"] = self.samples_per_step
        return parent_json_repr

    @classmethod
    def from_json(cls, json_data: Any) -> NStepUniformSampler:
        samples_per_step = json_data["samples_per_step"]
        return cls(samples_per_step)

    @classmethod
    def get_alias(cls) -> str:
        return "uniform"


ALIASES: dict[str, type[NStepSampler]] = {
    NStepUniformSampler.get_alias(): NStepUniformSampler
}
