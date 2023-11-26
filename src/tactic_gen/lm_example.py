from __future__ import annotations
from typing import Any, Type, Optional
from dataclasses import dataclass

from typeguard import typechecked

from tactic_gen.n_step_sampler import NStepSampler, OneStepSampler
from data_management.dataset_file import DatasetFile, FocusedStep, Proof, Sentence, Goal
from model_deployment.premise_model_wrapper import LocalPremiseModelWrapper

GOAL_SEP = "<G>"
PREM_SEP = "<P>"
THM_SEP = "<T>"
END_TOK = "<E>"
N_TAC_TOK = "<N>"


class LmExample:
    def __init__(self, input: str, output: str) -> None:
        self.input = input
        self.output = output

    def to_json(self) -> Any:
        return {
            "input": self.input,
            "output": self.output,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> LmExample:
        return cls(json_data["input"], json_data["output"])


def fmt_goals(goals: list[Goal]) -> str:
    goal_strings = [goal.to_string() for goal in goals]
    return GOAL_SEP.join(goal_strings)


class BasicFormatter:
    ALIAS = "basic"

    def __init__(self, n_step_sampler: NStepSampler, direct_num_steps: bool) -> None:
        self.n_step_sampler = n_step_sampler
        self.direct_num_steps = direct_num_steps

    def example_from_step(
        self, step_idx: int, proof: Proof, dp_obj: DatasetFile
    ) -> LmExample:
        step = proof.steps[step_idx]
        partial_proof_string = proof.proof_prefix_to_string(step)
        final_goal_string = fmt_goals(step.goals)
        input_prefix = f"{partial_proof_string}{THM_SEP}{final_goal_string}"
        n_step_sample = self.n_step_sampler.sample_steps(proof.steps[step_idx:])
        if self.direct_num_steps:
            input = f"{input_prefix}{N_TAC_TOK}{len(n_step_sample.steps)}"
        else:
            input = input_prefix
        output = "".join([fs.step.text for fs in n_step_sample.steps])
        return LmExample(input, output)


class PremiseFormatter:
    ALIAS = "premise"
    MAX_N_EXAMPLES = 100

    def __init__(
        self,
        premise_model_wrapper: LocalPremiseModelWrapper,
        n_step_sampler: NStepSampler,
        direct_num_steps: bool,
    ) -> None:
        self.premise_model_wrapper = premise_model_wrapper
        self.n_step_sampler = n_step_sampler
        self.direct_num_steps = direct_num_steps
        self.__basic_formatter = BasicFormatter(
            self.n_step_sampler, self.direct_num_steps
        )

    def get_premise_str(
        self,
        step: FocusedStep,
        proof: Proof,
        dp_obj: DatasetFile,
    ) -> str:
        filtered_result = (
            self.premise_model_wrapper.premise_filter.get_pos_and_avail_premises(
                step, proof, dp_obj
            )
        )
        ranked_premises = self.premise_model_wrapper.get_ranked_premise_generator(
            step, proof, filtered_result.avail_premises
        )
        top_premises: list[Sentence] = []
        for premise in ranked_premises:
            if len(top_premises) >= self.MAX_N_EXAMPLES:
                break
            top_premises.append(premise)

        premise_strs: list[str] = []
        for i, premise in enumerate(top_premises):
            premise_strs.append(f"Premise {i + 1}: {premise.text}")

        premise_strs.reverse()
        return "\n".join(premise_strs)

    def example_from_step(
        self, step_idx: int, proof: Proof, dp_obj: DatasetFile
    ) -> LmExample:
        step = proof.steps[step_idx]
        premise_str = self.get_premise_str(step, proof, dp_obj)
        basic_lm_example = self.__basic_formatter.example_from_step(
            step_idx, proof, dp_obj
        )
        input = f"{premise_str}{PREM_SEP}{basic_lm_example.input}"
        return LmExample(input, basic_lm_example.output)


class GoalFormatter:
    ALIAS = "goal-cotrain"

    def __init__(self, n_step_sampler: NStepSampler, direct_num_steps: bool) -> None:
        self.n_step_sampler = n_step_sampler
        self.direct_num_steps = direct_num_steps
        self.__basic_formatter = BasicFormatter(
            self.n_step_sampler, self.direct_num_steps
        )

    def example_from_step(
        self, step_idx: int, proof: Proof, dp_obj: DatasetFile
    ) -> LmExample:
        basic_example = self.__basic_formatter.example_from_step(
            step_idx, proof, dp_obj
        )
        n_step_result = self.n_step_sampler.sample_steps(proof.steps[step_idx:])
        output = (
            f"{basic_example.output}{END_TOK}{fmt_goals(n_step_result.resulting_goals)}"
        )
        return LmExample(basic_example.input, output)


class BaseCodeLLamaLmFormatter:
    ALIAS = "codellama-base"

    def example_from_step(
        self, step_idx: int, proof: Proof, partial_proof_suffix: Optional[str]
    ) -> LmExample:
        step = proof.steps[step_idx]
        goal_strings: list[str] = []
        for i, goal in enumerate(step.goals):
            goal_strings.append(f"Goal {i + 1}:\n{goal.to_string()}")
        partial_proof_string = proof.proof_prefix_to_string(step, include_proof=True)
        final_goal_string = "\n\n".join(goal_strings)
        input = f"{final_goal_string}\n\n{partial_proof_string}"
        output = step.step.text
        return LmExample(input, output)


class BaseCodeLLamaPremiseLmFormatter:
    ALIAS = "codellama-base-premise"

    def __init__(self, premise_model_wrapper: LocalPremiseModelWrapper) -> None:
        self.premise_model_wrapper = premise_model_wrapper
        self.__premise_formatter = PremiseFormatter(
            self.premise_model_wrapper, OneStepSampler(), False
        )

    def example_from_step(
        self,
        step_idx: int,
        proof: Proof,
        dset_obj: DatasetFile,
        partial_proof_suffix: Optional[str],
        premise_model_wrapper: LocalPremiseModelWrapper,
    ) -> LmExample:
        step = proof.steps[step_idx]
        goal_strings: list[str] = []
        for i, goal in enumerate(step.goals):
            goal_strings.append(f"Goal {i + 1}:\n{goal.to_string()}")
        partial_proof_string = proof.proof_prefix_to_string(step, include_proof=True)
        final_goal_string = "\n\n".join(goal_strings)
        premise_string = self.__premise_formatter.get_premise_str(step, proof, dset_obj)
        input = f"{premise_string}\n\n{final_goal_string}\n\n{partial_proof_string}"
        output = step.step.text
        return LmExample(input, output)


class GPT4Formatter:
    ALIAS = "gpt4"
    SCRIPT_TAG = "<PS>"
    STATE_TAG = "<ST>"
    SYS_MSG = (
        "You are given a partial coq proof following "
        f"the {SCRIPT_TAG} tag. You are given the proof "
        f"state of the partial proof following the {STATE_TAG} "
        "tag. You respond with the next coq command to use "
        "in order to eventually complete the proof. "
    )

    def example_from_step(
        self,
        step_idx: int,
        proof: Proof,
        dp_obj: DatasetFile,
    ) -> LmExample:
        step = proof.steps[step_idx]
        goal_strings: list[str] = []
        for i, goal in enumerate(step.goals):
            goal_strings.append(f"Goal {i + 1}\n{goal.to_string()}")
        partial_proof_string = proof.proof_prefix_to_string(step)
        final_goal_string = "\n".join(goal_strings)
        input = f"{self.SCRIPT_TAG}\n{partial_proof_string}\n{self.STATE_TAG}\n{final_goal_string}"
        output = step.step.text
        return LmExample(input, output)


LmExample = (
    BasicLmExample
    | GoalLmExample
    | AutoNTacticLmExample
    | BaseCodeLLamaLmExample
    | BaseCodeLLamaPremiseLmExample
    | GPT4BasicLmExample
)

LmFormatter = (
    BasicFormatter
    | PremiseFormatter
    | GoalFormatter
    | BaseCodeLLamaLmFormatter
    | BaseCodeLLamaPremiseLmFormatter
    | GPT4Formatter
)


LMEXAMPLE_ALIASES: dict[str, Type[LmExample]] = {
    BasicLmExample.get_alias(): BasicLmExample,
    GoalLmExample.get_alias(): GoalLmExample,
    GPT4BasicLmExample.get_alias(): GPT4BasicLmExample,
    PremiseLmExample.get_alias(): PremiseLmExample,
    AutoNTacticLmExample.get_alias(): AutoNTacticLmExample,
    BaseCodeLLamaLmExample.get_alias(): BaseCodeLLamaLmExample,
    BaseCodeLLamaPremiseLmExample.get_alias(): BaseCodeLLamaPremiseLmExample,
}
