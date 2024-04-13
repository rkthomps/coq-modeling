from __future__ import annotations
from typing import Any
from dataclasses import dataclass
from data_management.dataset_file import FocusedStep, Proof, DatasetFile
from tactic_gen.lm_example import fmt_goals


@dataclass
class GoalExample:
    goal: str
    n_step_left: int

    def to_json(self) -> Any:
        return {
            "goal": self.goal,
            "n_step_left": self.n_step_left,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> GoalExample:
        return cls(json_data["goal"], json_data["n_step_left"])


@dataclass
class GoalFormatterConf:
    @classmethod
    def from_yaml(cls, yaml_data: Any) -> GoalFormatterConf:
        return cls()


class GoalFormatter:
    def example_from_step(
        self, step_idx: int, proof: Proof
    ) -> GoalExample:
        step = proof.steps[step_idx]
        goal_str = fmt_goals(step.goals)
        n_steps_left = len(proof.steps) - step_idx
        return GoalExample(goal_str, n_steps_left)

    @classmethod
    def from_conf(cls, conf: GoalFormatterConf) -> GoalFormatter:
        return GoalFormatter()
