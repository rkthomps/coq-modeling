from __future__ import annotations
from typing import Any
import time

from dataclasses import dataclass
from typeguard import typechecked

from tactic_gen.proof_distance import SortedProofs, StrippedProof
from tactic_gen.n_step_sampler import NStepSampler, OneStepSampler, n_step_from_conf
from data_management.dataset_file import DatasetFile, FocusedStep, Proof, Sentence, Goal
from model_deployment.premise_model_wrapper import (
    PremiseModelWrapper,
    get_ranked_premise_generator,
    premise_wrapper_from_conf,
)
from util.util import get_basic_logger

_logger = get_basic_logger(__name__)

GOAL_SEP = "<G>"
PREM_SEP = "<P>"
PROOF_RET_SEP = "<F>"
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

    def __init__(
        self, n_step_sampler: NStepSampler, direct_num_steps: bool, conf: Any
    ) -> None:
        self.n_step_sampler = n_step_sampler
        self.direct_num_steps = direct_num_steps
        self.conf = conf

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

    @classmethod
    def from_conf(cls, conf: Any) -> BasicFormatter:
        n_step_sampler = n_step_from_conf(conf["n_step_sampler"])
        direct_num_steps = conf["direct_num_steps"]
        return cls(n_step_sampler, direct_num_steps, conf)


class PremiseFormatter:
    ALIAS = "premise"
    MAX_N_EXAMPLES = 100

    def __init__(
        self,
        premise_model_wrapper: PremiseModelWrapper,
        n_step_sampler: NStepSampler,
        direct_num_steps: bool,
        conf: Any,
    ) -> None:
        self.premise_model_wrapper = premise_model_wrapper
        self.n_step_sampler = n_step_sampler
        self.direct_num_steps = direct_num_steps
        self.__basic_formatter = BasicFormatter(
            self.n_step_sampler, self.direct_num_steps, conf
        )
        self.conf = conf

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
        ranked_premises = get_ranked_premise_generator(
            self.premise_model_wrapper, step, proof, filtered_result.avail_premises
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

    @classmethod
    def from_conf(cls, conf: Any) -> PremiseFormatter:
        premise_model_wrapper = premise_wrapper_from_conf(conf["premise_model_wrapper"])
        tmp_basic_formatter = BasicFormatter.from_conf(conf)
        return cls(
            premise_model_wrapper,
            tmp_basic_formatter.n_step_sampler,
            tmp_basic_formatter.direct_num_steps,
            conf,
        )


class ProofRetrievalOricleFormatter:
    ALIAS = "proof-retrieval-oricle"

    def __init__(
        self,
        n_step_sampler: NStepSampler,
        direct_num_steps: bool,
        sorted_proofs: SortedProofs,
        conf: Any,
    ) -> None:
        self.n_step_sampler = n_step_sampler
        self.direct_num_steps = direct_num_steps
        self.sorted_proofs = sorted_proofs
        self.conf = conf
        self.__basic_formatter = BasicFormatter(n_step_sampler, direct_num_steps, conf)

    def example_from_step(
        self, step_idx: int, proof: Proof, dp_obj: DatasetFile
    ) -> LmExample:
        """TODO: MAY NEED TO PASS IN FILEINFO OR SOMETHING TO THIS"""
        basic_lm_example = self.__basic_formatter.example_from_step(
            step_idx, proof, dp_obj
        )
        stripped_proof = StrippedProof.from_steps([s.step.text for s in proof.steps])
        start = time.time()
        similar_proof = self.sorted_proofs.nearest(stripped_proof)
        end = time.time()
        _logger.debug("Retrieved proof in {:5.3f} seconds".format(end - start))
        new_input = (
            f"{similar_proof.proof.to_string()}{PROOF_RET_SEP}{basic_lm_example.input}"
        )
        return LmExample(new_input, basic_lm_example.output)


class GoalFormatter:
    ALIAS = "goal-cotrain"
    STOP_STRINGS = [END_TOK]

    def __init__(
        self, n_step_sampler: NStepSampler, direct_num_steps: bool, conf: Any
    ) -> None:
        self.n_step_sampler = n_step_sampler
        self.direct_num_steps = direct_num_steps
        self.__basic_formatter = BasicFormatter(
            self.n_step_sampler, self.direct_num_steps, conf
        )
        self.conf = conf

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

    @classmethod
    def from_conf(cls, conf: Any) -> GoalFormatter:
        tmp_basic_formatter = BasicFormatter.from_conf(conf)
        return cls(
            tmp_basic_formatter.n_step_sampler,
            tmp_basic_formatter.direct_num_steps,
            conf,
        )


class BaseCodeLLamaLmFormatter:
    ALIAS = "codellama-base"

    def example_from_step(
        self, step_idx: int, proof: Proof, dp_obj: DatasetFile
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

    def __init__(self, premise_model_wrapper: PremiseModelWrapper, conf: Any) -> None:
        self.premise_model_wrapper = premise_model_wrapper
        self.__premise_formatter = PremiseFormatter(
            self.premise_model_wrapper, OneStepSampler(), False, conf
        )
        self.conf = conf

    def example_from_step(
        self,
        step_idx: int,
        proof: Proof,
        dset_obj: DatasetFile,
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

    @classmethod
    def from_conf(cls, conf: Any) -> BaseCodeLLamaPremiseLmFormatter:
        premise_model_wrapper = premise_wrapper_from_conf(conf["premise_model_wrapper"])
        return cls(premise_model_wrapper, conf)


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


LmFormatter = (
    BasicFormatter
    | PremiseFormatter
    | GoalFormatter
    | BaseCodeLLamaLmFormatter
    | BaseCodeLLamaPremiseLmFormatter
    | GPT4Formatter
)


class LmFormatterNotFoundError(Exception):
    pass


def fmt_from_conf(conf: Any) -> LmFormatter:
    attempted_alias = conf["alias"]
    match attempted_alias:
        case BasicFormatter.ALIAS:
            return BasicFormatter.from_conf(conf)
        case PremiseFormatter.ALIAS:
            return PremiseFormatter.from_conf(conf)
        case GoalFormatter.ALIAS:
            return GoalFormatter.from_conf(conf)
        case BaseCodeLLamaLmFormatter.ALIAS:
            return BaseCodeLLamaLmFormatter()
        case BaseCodeLLamaPremiseLmFormatter.ALIAS:
            return BaseCodeLLamaPremiseLmFormatter.from_conf(conf)
        case GPT4Formatter.ALIAS:
            return GPT4Formatter()
        case _:
            raise LmFormatterNotFoundError(
                f"Could not find Lm Formatter: {attempted_alias}"
            )


def fmt_get_conf(formatter: LmFormatter) -> Any:
    match formatter:
        case BasicFormatter() | PremiseFormatter() | GoalFormatter() | BaseCodeLLamaPremiseLmFormatter():
            return formatter.conf
        case BaseCodeLLamaLmFormatter() | GPT4Formatter():
            return None


def fmt_get_stop_strings(formatter: LmFormatter) -> list[str]:
    match formatter:
        case GoalFormatter():
            return GoalFormatter.STOP_STRINGS
        case _:
            return []
