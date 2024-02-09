from __future__ import annotations
from typing import Any, Optional
import time
import datetime
import os

from dataclasses import dataclass
from typeguard import typechecked
from transformers import CodeLlamaTokenizer

from data_management.splits import FileInfo, Split
from data_management.dataset_file import DatasetFile, FocusedStep, Proof, Sentence, Goal
from tactic_gen.proof_distance import SortedProofs, StrippedProof
from tactic_gen.n_step_sampler import NStepSampler, OneStepSampler, n_step_from_conf
from tactic_gen.step_parser import norm, CoqParseError
from model_deployment.premise_model_wrapper import (
    PremiseModelWrapper,
    move_prem_wrapper_to,
    get_ranked_premise_generator,
    premise_wrapper_from_conf,
)
from model_deployment.mine_goals import FileGoals, GoalRecord
from util.util import get_basic_logger

_logger = get_basic_logger(__name__)

GOAL_SEP = "<G>"
PREM_SEP = "<P>"
PROOF_RET_SEP = "<F>"
STMT_SEP = "<S>"
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
    REQUIRES_GPU = False

    def __init__(
        self, n_step_sampler: NStepSampler, direct_num_steps: bool, conf: Any
    ) -> None:
        self.n_step_sampler = n_step_sampler
        self.direct_num_steps = direct_num_steps
        self.conf = conf

    def example_from_step(
        self,
        step_idx: int,
        proof: Proof,
        dp_obj: DatasetFile,
        file_info: FileInfo,
        split: Split,
        data_loc: str,
        ground_truth_steps: Optional[list[str]],
    ) -> LmExample:
        ground_truth_steps = None
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


def allocate_tokens(
    tokenizer: CodeLlamaTokenizer, s: str, allowance: int, truncate_front=True
) -> tuple[str, int]:
    tokens = tokenizer.encode(s)
    if truncate_front:
        to_add = tokens[(-1 * allowance) :]
    else:
        to_add = tokens[:allowance]
    return tokenizer.decode(to_add, skip_special_tokens=True), len(to_add)


class ProofRetrievalFormatter:
    ALIAS = "proof-ret"

    def __init__(
        self,
        proof_bank_loc: str,
        tokenizer: CodeLlamaTokenizer,
        state_num_tokens: int,
        script_num_tokens: int,
        statement_num_tokens: int,
        ret_proof_state_tokens: int,
        ret_proof_script_tokens: int,
        n_step_sampler: NStepSampler,
        direct_num_steps: bool,
        conf: Any,
    ) -> None:
        self.proof_bank_loc = proof_bank_loc
        self.__proof_bank: dict[str, FileGoals] = {}
        self.tokenizer = tokenizer
        self.state_num_tokens = state_num_tokens
        self.script_num_tokens = script_num_tokens
        self.statement_num_tokens = statement_num_tokens
        self.ret_proof_state_tokens = ret_proof_state_tokens
        self.ret_proof_script_tokens = ret_proof_script_tokens
        self.n_step_sampler = n_step_sampler
        self.direct_num_steps = direct_num_steps
        self.conf = conf

    def __get_file_goals(self, key: str) -> Optional[FileGoals]:
        if key in self.__proof_bank:
            return self.__proof_bank[key]
        goal_loc = os.path.join(self.proof_bank_loc, key)
        if not os.path.exists(goal_loc):
            return None
        goals = FileGoals.load(goal_loc)
        self.__proof_bank[key] = goals
        return goals

    def get_current_goal_similar_in_file_goal(
        self, step_idx: int, proof: Proof, file_goals: FileGoals
    ) -> Optional[tuple[GoalRecord, Optional[tuple[int, GoalRecord]]]]:
        current_ground_truth = [s.step.text for s in proof.steps[step_idx:]]
        complete_ground_truth = [s.step.text for s in proof.steps]
        prefix_len = len(complete_ground_truth) - len(current_ground_truth)
        record_idx: Optional[int] = None
        for i, record in enumerate(file_goals.records):
            if record.proof == current_ground_truth:
                record_idx = i
                break
        if record_idx is None:
            return None
        current_record = file_goals.records[record_idx]
        similar_candidate: Optional[tuple[int, GoalRecord]] = None
        proof_start_idx = current_record.step_idx - prefix_len
        for record in file_goals.records[:record_idx]:
            if proof_start_idx <= record.step_idx: 
                break
            # # If you wanted to be able to retrieve from completed subgoals: 
            # if current_record.step_idx <= record.step_idx + len(record.proof):
            #     continue
            if similar_candidate:
                sim_dist, _ = similar_candidate
                new_dist = current_record.term.distance(
                    record.term, abort_at_distance=sim_dist
                )
                if new_dist < sim_dist:
                    similar_candidate = new_dist, record
            else:
                new_dist = current_record.term.distance(record.term)
                similar_candidate = new_dist, record
        return current_record, similar_candidate

    def get_similar_proof(
        self, step_idx: int, proof: Proof, dp_obj: DatasetFile, file_info: FileInfo
    ) -> Optional[tuple[str, list[str]]]:
        """Returns most similar proof state and proof script"""
        file_goals = self.__get_file_goals(file_info.dp_name)
        if file_goals is None:
            return None
        record_and_best_in_file = self.get_current_goal_similar_in_file_goal(
            step_idx, proof, file_goals
        )
        if record_and_best_in_file is None:
            return None
        current_record, similar_candidate = record_and_best_in_file
        for dependency in dp_obj.dependencies:
            dependency_goals = self.__get_file_goals(dependency)
            if dependency_goals is None:
                continue
            for record in dependency_goals.records:
                if similar_candidate:
                    cur_dist, _ = similar_candidate
                    new_dist = current_record.term.distance(
                        record.term, abort_at_distance=cur_dist
                    )
                    if new_dist < cur_dist:
                        similar_candidate = new_dist, record
                else:
                    new_dist = current_record.term.distance(record.term)
                    similar_candidate = new_dist, record
        if similar_candidate:
            _, best_record = similar_candidate
            return best_record.pretty_goal, best_record.proof
        return None

    def example_from_step(
        self,
        step_idx: int,
        proof: Proof,
        dp_obj: DatasetFile,
        file_info: FileInfo,
        split: Split,
        data_loc: str,
        ground_truth_steps: Optional[list[str]],
    ) -> LmExample:
        step = proof.steps[step_idx]
        similar_proof_result = self.get_similar_proof(
            step_idx, proof, dp_obj, file_info
        )
        if similar_proof_result:
            similar_proof_state, similar_proof_script = similar_proof_result
            ret_state_str = allocate_tokens(
                self.tokenizer, similar_proof_state, self.ret_proof_state_tokens
            )
            ret_script_str = allocate_tokens(
                self.tokenizer,
                "".join(similar_proof_script),
                self.ret_proof_script_tokens,
                truncate_front=False,
            )
        else:
            ret_state_str = ""
            ret_script_str = ""

        statement, _ = allocate_tokens(
            self.tokenizer,
            proof.theorem.term.text,
            self.statement_num_tokens,
            truncate_front=False,
        )

        partial_proof_string = proof.proof_prefix_to_string(step, include_theorem=False)
        proof_str, _ = allocate_tokens(
            self.tokenizer, partial_proof_string, self.script_num_tokens
        )

        final_goal_string = fmt_goals(step.goals)
        state_str, _ = allocate_tokens(
            self.tokenizer, final_goal_string, self.state_num_tokens
        )

        input_prefix = f"{ret_state_str}{PROOF_RET_SEP}{ret_script_str}{PREM_SEP}{statement}{STMT_SEP}{proof_str}{THM_SEP}{state_str}"
        n_step_sample = self.n_step_sampler.sample_steps(proof.steps[step_idx:])

        if self.direct_num_steps:
            input = f"{input_prefix}{N_TAC_TOK}{len(n_step_sample.steps)}"
        else:
            input = input_prefix
        output = "".join([fs.step.text for fs in n_step_sample.steps])
        return LmExample(input, output)


class OptimalPremiseFormatter:
    ALIAS = "optim-premise"

    def __init__(
        self,
        tokenizer: CodeLlamaTokenizer,
        state_num_tokens: int,
        script_num_tokens: int,
        statement_num_tokens: int,
        premise_num_tokens: int,
        n_step_sampler: NStepSampler,
        direct_num_steps: bool,
        conf: Any,
    ) -> None:
        self.tokenizer = tokenizer
        self.state_num_tokens = state_num_tokens
        self.script_num_tokens = script_num_tokens
        self.statement_num_tokens = statement_num_tokens
        self.premise_num_tokens = premise_num_tokens
        self.n_step_sampler = n_step_sampler
        self.direct_num_steps = direct_num_steps
        self.conf = conf

    def _sort_premises(self, premises: list[Sentence]) -> list[Sentence]:
        coq_premises: list[Sentence] = []
        non_coq_premises: list[Sentence] = []
        coq_lib_str = os.path.join("lib", "coq", "theories") + "/"
        for premise in premises:
            if coq_lib_str in premise.file_path:
                coq_premises.append(premise)
            else:
                non_coq_premises.append(premise)
        return non_coq_premises + coq_premises

    def example_from_step(
        self,
        step_idx: int,
        proof: Proof,
        dp_obj: DatasetFile,
        file_info: FileInfo,
        split: Split,
        data_loc: str,
        ground_truth_steps: Optional[list[str]],
    ) -> LmExample:
        step = proof.steps[step_idx]
        step_premises = step.step.context
        total_premise_tokens = 0
        premises: list[str] = []
        for premise in self._sort_premises(step_premises):
            allowance = self.premise_num_tokens - total_premise_tokens
            if allowance <= 0:
                break
            trunc_str, num_toks = allocate_tokens(
                self.tokenizer, premise.text, allowance, truncate_front=False
            )
            premises.append(trunc_str)
            total_premise_tokens += num_toks
        premise_str = "\n".join(premises)

        statement, _ = allocate_tokens(
            self.tokenizer,
            proof.theorem.term.text,
            self.statement_num_tokens,
            truncate_front=False,
        )

        partial_proof_string = proof.proof_prefix_to_string(step, include_theorem=False)
        proof_str, _ = allocate_tokens(
            self.tokenizer, partial_proof_string, self.script_num_tokens
        )

        final_goal_string = fmt_goals(step.goals)
        state_str, _ = allocate_tokens(
            self.tokenizer, final_goal_string, self.state_num_tokens
        )

        input_prefix = f"{premise_str}{PREM_SEP}{statement}{STMT_SEP}{proof_str}{THM_SEP}{state_str}"
        n_step_sample = self.n_step_sampler.sample_steps(proof.steps[step_idx:])

        if self.direct_num_steps:
            input = f"{input_prefix}{N_TAC_TOK}{len(n_step_sample.steps)}"
        else:
            input = input_prefix
        output = "".join([fs.step.text for fs in n_step_sample.steps])
        return LmExample(input, output)

    @classmethod
    def from_conf(cls, conf: Any) -> OptimalPremiseFormatter:
        model_name = conf["model_name"]
        tokenizer = CodeLlamaTokenizer.from_pretrained(model_name, use_fast=True)
        state_num_tokens = conf["state_num_tokens"]
        script_num_tokens = conf["script_num_tokens"]
        statement_num_tokens = conf["statement_num_tokens"]
        premise_num_tokens = conf["premise_num_tokens"]
        tmp_basic_formatter = BasicFormatter.from_conf(conf)
        return cls(
            tokenizer,
            state_num_tokens,
            script_num_tokens,
            statement_num_tokens,
            premise_num_tokens,
            tmp_basic_formatter.n_step_sampler,
            tmp_basic_formatter.direct_num_steps,
            conf,
        )


class GroundTruthLeakFormatter:
    ALIAS = "ground-truth"

    def __init__(
        self,
        tokenizer: CodeLlamaTokenizer,
        state_num_tokens: int,
        script_num_tokens: int,
        statement_num_tokens: int,
        ground_truth_num_tokens: int,
        n_step_sampler: NStepSampler,
        direct_num_steps: bool,
        conf: Any,
    ) -> None:
        self.tokenizer = tokenizer
        self.state_num_tokens = state_num_tokens
        self.script_num_tokens = script_num_tokens
        self.statement_num_tokens = statement_num_tokens
        self.ground_truth_num_tokens = ground_truth_num_tokens
        self.n_step_sampler = n_step_sampler
        self.direct_num_steps = direct_num_steps
        self.conf = conf

    def example_from_step(
        self,
        step_idx: int,
        proof: Proof,
        dp_obj: DatasetFile,
        file_info: FileInfo,
        split: Split,
        data_loc: str,
        ground_truth_steps: Optional[list[str]],
    ) -> LmExample:
        assert ground_truth_steps is not None
        step = proof.steps[step_idx]
        ground_truth_str, _ = allocate_tokens(
            self.tokenizer,
            "".join(ground_truth_steps[step_idx:]),
            self.ground_truth_num_tokens,
            truncate_front=True,
        )

        statement, _ = allocate_tokens(
            self.tokenizer,
            proof.theorem.term.text,
            self.statement_num_tokens,
            truncate_front=False,
        )

        partial_proof_string = proof.proof_prefix_to_string(step, include_theorem=False)
        proof_str, _ = allocate_tokens(
            self.tokenizer, partial_proof_string, self.script_num_tokens
        )

        final_goal_string = fmt_goals(step.goals)
        state_str, _ = allocate_tokens(
            self.tokenizer, final_goal_string, self.state_num_tokens
        )

        input_prefix = f"{ground_truth_str}{PREM_SEP}{statement}{STMT_SEP}{proof_str}{THM_SEP}{state_str}"
        n_step_sample = self.n_step_sampler.sample_steps(proof.steps[step_idx:])

        if self.direct_num_steps:
            input = f"{input_prefix}{N_TAC_TOK}{len(n_step_sample.steps)}"
        else:
            input = input_prefix
        output = "".join([fs.step.text for fs in n_step_sample.steps])
        return LmExample(input, output)

    @classmethod
    def from_conf(cls, conf: Any) -> GroundTruthLeakFormatter:
        model_name = conf["model_name"]
        tokenizer = CodeLlamaTokenizer.from_pretrained(model_name, use_fast=True)
        state_num_tokens = conf["state_num_tokens"]
        script_num_tokens = conf["script_num_tokens"]
        statement_num_tokens = conf["statement_num_tokens"]
        ground_truth_num_tokens = conf["ground_truth_num_tokens"]
        tmp_basic_formatter = BasicFormatter.from_conf(conf)
        return cls(
            tokenizer,
            state_num_tokens,
            script_num_tokens,
            statement_num_tokens,
            ground_truth_num_tokens,
            tmp_basic_formatter.n_step_sampler,
            tmp_basic_formatter.direct_num_steps,
            conf,
        )


class FixedPremiseFormatter:
    ALIAS = "fixed-premise"

    def __init__(
        self,
        premise_model_wrapper: PremiseModelWrapper,
        tokenizer: CodeLlamaTokenizer,
        state_num_tokens: int,
        script_num_tokens: int,
        statement_num_tokens: int,
        premise_num_tokens: int,
        n_step_sampler: NStepSampler,
        direct_num_steps: bool,
        conf: Any,
    ) -> None:
        self.premise_model_wrapper = premise_model_wrapper
        self.tokenizer = tokenizer
        self.state_num_tokens = state_num_tokens
        self.script_num_tokens = script_num_tokens
        self.statement_num_tokens = statement_num_tokens
        self.premise_num_tokens = premise_num_tokens
        self.n_step_sampler = n_step_sampler
        self.direct_num_steps = direct_num_steps
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
        total_premise_tokens = 0
        premises: list[str] = []
        for premise in ranked_premises:
            allowance = self.premise_num_tokens - total_premise_tokens
            if allowance <= 0:
                break
            trunc_str, num_toks = allocate_tokens(
                self.tokenizer, premise.text, allowance, truncate_front=False
            )
            premises.insert(0, trunc_str)
            total_premise_tokens += num_toks
        return "\n".join(premises)

    def example_from_step(
        self,
        step_idx: int,
        proof: Proof,
        dp_obj: DatasetFile,
        file_info: FileInfo,
        split: Split,
        data_loc: str,
        ground_truth_steps: Optional[list[str]],
    ) -> LmExample:
        step = proof.steps[step_idx]
        premise_str = self.get_premise_str(step, proof, dp_obj)

        statement, _ = allocate_tokens(
            self.tokenizer,
            proof.theorem.term.text,
            self.statement_num_tokens,
            truncate_front=False,
        )

        partial_proof_string = proof.proof_prefix_to_string(step, include_theorem=False)
        proof_str, _ = allocate_tokens(
            self.tokenizer, partial_proof_string, self.script_num_tokens
        )

        final_goal_string = fmt_goals(step.goals)
        state_str, _ = allocate_tokens(
            self.tokenizer, final_goal_string, self.state_num_tokens
        )

        input_prefix = f"{premise_str}{PREM_SEP}{statement}{STMT_SEP}{proof_str}{THM_SEP}{state_str}"
        n_step_sample = self.n_step_sampler.sample_steps(proof.steps[step_idx:])

        if self.direct_num_steps:
            input = f"{input_prefix}{N_TAC_TOK}{len(n_step_sample.steps)}"
        else:
            input = input_prefix
        output = "".join([fs.step.text for fs in n_step_sample.steps])
        return LmExample(input, output)

    @classmethod
    def from_conf(cls, conf: Any) -> FixedPremiseFormatter:
        model_name = conf["model_name"]
        tokenizer = CodeLlamaTokenizer.from_pretrained(model_name, use_fast=True)
        premise_model_wrapper = premise_wrapper_from_conf(conf["premise_model_wrapper"])
        state_num_tokens = conf["state_num_tokens"]
        script_num_tokens = conf["script_num_tokens"]
        statement_num_tokens = conf["statement_num_tokens"]
        premise_num_tokens = conf["premise_num_tokens"]
        tmp_basic_formatter = BasicFormatter.from_conf(conf)
        return cls(
            premise_model_wrapper,
            tokenizer,
            state_num_tokens,
            script_num_tokens,
            statement_num_tokens,
            premise_num_tokens,
            tmp_basic_formatter.n_step_sampler,
            tmp_basic_formatter.direct_num_steps,
            conf,
        )


class StatementPremiseFormatter:
    ALIAS = "thm-premise"

    def __init__(
        self,
        tokenizer: CodeLlamaTokenizer,
        state_num_tokens: int,
        script_num_tokens: int,
        statement_num_tokens: int,
        premise_num_tokens: int,
        n_step_sampler: NStepSampler,
        direct_num_steps: bool,
        conf: Any,
    ) -> None:
        self.tokenizer = tokenizer
        self.state_num_tokens = state_num_tokens
        self.script_num_tokens = script_num_tokens
        self.statement_num_tokens = statement_num_tokens
        self.premise_num_tokens = premise_num_tokens
        self.n_step_sampler = n_step_sampler
        self.direct_num_steps = direct_num_steps
        self.conf = conf

    def _sort_premises(self, premises: list[Sentence]) -> list[Sentence]:
        coq_premises: list[Sentence] = []
        non_coq_premises: list[Sentence] = []
        coq_lib_str = os.path.join("lib", "coq", "theories") + "/"
        for premise in premises:
            if coq_lib_str in premise.file_path:
                coq_premises.append(premise)
            else:
                non_coq_premises.append(premise)
        return non_coq_premises + coq_premises

    def example_from_step(
        self,
        step_idx: int,
        proof: Proof,
        dp_obj: DatasetFile,
        file_info: FileInfo,
        split: Split,
        data_loc: str,
        ground_truth_steps: Optional[list[str]],
    ) -> LmExample:
        step = proof.steps[step_idx]
        thm_context = proof.theorem.term_context
        total_premise_tokens = 0
        premises: list[str] = []
        for premise in self._sort_premises(thm_context):
            allowance = self.premise_num_tokens - total_premise_tokens
            if allowance <= 0:
                break
            trunc_str, num_toks = allocate_tokens(
                self.tokenizer, premise.text, allowance, truncate_front=False
            )
            premises.append(trunc_str)
            total_premise_tokens += num_toks
        premise_str = "\n".join(premises)

        statement, _ = allocate_tokens(
            self.tokenizer,
            proof.theorem.term.text,
            self.statement_num_tokens,
            truncate_front=False,
        )

        partial_proof_string = proof.proof_prefix_to_string(step, include_theorem=False)
        proof_str, _ = allocate_tokens(
            self.tokenizer, partial_proof_string, self.script_num_tokens
        )

        final_goal_string = fmt_goals(step.goals)
        state_str, _ = allocate_tokens(
            self.tokenizer, final_goal_string, self.state_num_tokens
        )

        input_prefix = f"{premise_str}{PREM_SEP}{statement}{STMT_SEP}{proof_str}{THM_SEP}{state_str}"
        n_step_sample = self.n_step_sampler.sample_steps(proof.steps[step_idx:])

        if self.direct_num_steps:
            input = f"{input_prefix}{N_TAC_TOK}{len(n_step_sample.steps)}"
        else:
            input = input_prefix
        output = "".join([fs.step.text for fs in n_step_sample.steps])
        return LmExample(input, output)

    @classmethod
    def from_conf(cls, conf: Any) -> StatementPremiseFormatter:
        model_name = conf["model_name"]
        tokenizer = CodeLlamaTokenizer.from_pretrained(model_name, use_fast=True)
        state_num_tokens = conf["state_num_tokens"]
        script_num_tokens = conf["script_num_tokens"]
        statement_num_tokens = conf["statement_num_tokens"]
        premise_num_tokens = conf["premise_num_tokens"]
        tmp_basic_formatter = BasicFormatter.from_conf(conf)
        return cls(
            tokenizer,
            state_num_tokens,
            script_num_tokens,
            statement_num_tokens,
            premise_num_tokens,
            tmp_basic_formatter.n_step_sampler,
            tmp_basic_formatter.direct_num_steps,
            conf,
        )


class PremiseFormatter:
    ALIAS = "premise"
    REQUIRES_GPU = True
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
        self,
        step_idx: int,
        proof: Proof,
        dp_obj: DatasetFile,
        file_info: FileInfo,
        split: Split,
        data_loc: str,
        ground_truth_steps: Optional[list[str]],
    ) -> LmExample:
        ground_truth_steps = None
        step = proof.steps[step_idx]
        premise_str = self.get_premise_str(step, proof, dp_obj)
        basic_lm_example = self.__basic_formatter.example_from_step(
            step_idx, proof, dp_obj, file_info, split, data_loc, ground_truth_steps
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


class ProofRetrievalOracleFormatter:
    ALIAS = "proof-retrieval-oracle"
    REQUIRES_GPU = False

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
        self.__cached_similar_proofs: dict[tuple[str, int], StrippedProof] = {}
        self.__cached_times: dict[FileInfo, datetime.datetime] = {}

    def __get_proof_key(self, proof: Proof, file_info: FileInfo) -> tuple[str, int]:
        return file_info.file, proof.theorem.term.line

    def example_from_step(
        self,
        step_idx: int,
        proof: Proof,
        dp_obj: DatasetFile,
        file_info: FileInfo,
        split: Split,
        data_loc: str,
        ground_truth_steps: Optional[list[str]],
    ) -> LmExample:
        """TODO: MAY NEED TO PASS IN FILEINFO OR SOMETHING TO THIS"""
        assert ground_truth_steps is not None
        basic_lm_example = self.__basic_formatter.example_from_step(
            step_idx, proof, dp_obj, file_info, split, data_loc, ground_truth_steps
        )
        if file_info in self.__cached_times:
            creation_time = self.__cached_times[file_info]
        else:
            creation_time = file_info.get_creation_time(data_loc)
            self.__cached_times[file_info] = creation_time
        proof_key = self.__get_proof_key(proof, file_info)
        if proof_key in self.__cached_similar_proofs:
            similar_proof = self.__cached_similar_proofs[proof_key]
        else:
            try:
                norm_steps = [norm(s) for s in ground_truth_steps]
            except CoqParseError:
                norm_steps = None
            stripped_proof = StrippedProof(
                creation_time,
                file_info,
                proof.theorem.term.line,
                proof.theorem.term.text,
                ground_truth_steps,
                norm_steps,
                split,
            )
            start = time.time()
            similar_proof = self.sorted_proofs.nearest(stripped_proof).proof
            end = time.time()
            _logger.debug("Retrieved proof in {:5.3f} seconds".format(end - start))
            self.__cached_similar_proofs[proof_key] = similar_proof

        new_input = (
            f"{similar_proof.to_string()}{PROOF_RET_SEP}{basic_lm_example.input}"
        )
        return LmExample(new_input, basic_lm_example.output)

    @classmethod
    def from_conf(cls, conf: Any) -> ProofRetrievalOracleFormatter:
        tmp_basic_formatter = BasicFormatter.from_conf(conf)
        _logger.debug("Loading similar proof database.")
        sorted_proofs = SortedProofs.load(conf["sorted_proof_loc"])
        return cls(
            tmp_basic_formatter.n_step_sampler,
            tmp_basic_formatter.direct_num_steps,
            sorted_proofs,
            conf,
        )


class GoalFormatter:
    ALIAS = "goal-cotrain"
    REQUIRES_GPU = False
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
        self,
        step_idx: int,
        proof: Proof,
        dp_obj: DatasetFile,
        file_info: FileInfo,
        split: Split,
        data_loc: str,
        ground_truth_steps: Optional[list[str]],
    ) -> LmExample:
        ground_truth_steps = None
        basic_example = self.__basic_formatter.example_from_step(
            step_idx, proof, dp_obj, file_info, split, data_loc, ground_truth_steps
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
    REQUIRES_GPU = False

    def example_from_step(
        self,
        step_idx: int,
        proof: Proof,
        dp_obj: DatasetFile,
        file_info: FileInfo,
        split: Split,
        data_loc: str,
        ground_truth_steps: Optional[list[str]],
    ) -> LmExample:
        ground_truth_steps = None
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
    REQUIRES_GPU = True

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
        dp_obj: DatasetFile,
        file_info: FileInfo,
        split: Split,
        data_loc: str,
        ground_truth_steps: Optional[list[str]],
    ) -> LmExample:
        ground_truth_steps = None
        step = proof.steps[step_idx]
        goal_strings: list[str] = []
        for i, goal in enumerate(step.goals):
            goal_strings.append(f"Goal {i + 1}:\n{goal.to_string()}")
        partial_proof_string = proof.proof_prefix_to_string(step, include_proof=True)
        final_goal_string = "\n\n".join(goal_strings)
        premise_string = self.__premise_formatter.get_premise_str(step, proof, dp_obj)
        input = f"{premise_string}\n\n{final_goal_string}\n\n{partial_proof_string}"
        output = step.step.text
        return LmExample(input, output)

    @classmethod
    def from_conf(cls, conf: Any) -> BaseCodeLLamaPremiseLmFormatter:
        premise_model_wrapper = premise_wrapper_from_conf(conf["premise_model_wrapper"])
        return cls(premise_model_wrapper, conf)


class GPT4Formatter:
    ALIAS = "gpt4"
    REQUIRES_GPU = False
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
        file_info: FileInfo,
        split: Split,
        data_loc: str,
        ground_truth_steps: Optional[list[str]],
    ) -> LmExample:
        ground_truth_steps = None
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
    | OptimalPremiseFormatter
    | StatementPremiseFormatter
    | GroundTruthLeakFormatter
    | FixedPremiseFormatter
    | PremiseFormatter
    | GoalFormatter
    | ProofRetrievalOracleFormatter
    | BaseCodeLLamaLmFormatter
    | BaseCodeLLamaPremiseLmFormatter
    | GPT4Formatter
)


class LmFormatterNotFoundError(Exception):
    pass


def move_fmt_to(formatter: LmFormatter, device: str) -> None:
    match formatter:
        case (
            BasicFormatter()
            | GroundTruthLeakFormatter()
            | StatementPremiseFormatter()
            | OptimalPremiseFormatter()
            | ProofRetrievalOracleFormatter()
            | GoalFormatter()
            | BaseCodeLLamaLmFormatter()
            | GPT4Formatter()
        ):
            pass
        case (
            FixedPremiseFormatter()
            | PremiseFormatter()
            | BaseCodeLLamaPremiseLmFormatter()
        ):
            move_prem_wrapper_to(formatter.premise_model_wrapper, device)


def fmt_from_conf(conf: Any) -> LmFormatter:
    attempted_alias = conf["alias"]
    match attempted_alias:
        case BasicFormatter.ALIAS:
            return BasicFormatter.from_conf(conf)
        case OptimalPremiseFormatter.ALIAS:
            return OptimalPremiseFormatter.from_conf(conf)
        case GroundTruthLeakFormatter.ALIAS:
            return GroundTruthLeakFormatter.from_conf(conf)
        case StatementPremiseFormatter.ALIAS:
            return StatementPremiseFormatter.from_conf(conf)
        case FixedPremiseFormatter.ALIAS:
            return FixedPremiseFormatter.from_conf(conf)
        case PremiseFormatter.ALIAS:
            return PremiseFormatter.from_conf(conf)
        case ProofRetrievalOracleFormatter.ALIAS:
            return ProofRetrievalOracleFormatter.from_conf(conf)
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
                f'Could not find Lm Formatter: "{attempted_alias}"'
            )


def fmt_get_conf(formatter: LmFormatter) -> Any:
    match formatter:
        case (
            BasicFormatter()
            | OptimalPremiseFormatter()
            | GroundTruthLeakFormatter()
            | StatementPremiseFormatter()
            | FixedPremiseFormatter()
            | PremiseFormatter()
            | GoalFormatter()
            | ProofRetrievalOracleFormatter()
            | BaseCodeLLamaPremiseLmFormatter()
        ):
            return formatter.conf
        case BaseCodeLLamaLmFormatter() | GPT4Formatter():
            return None


def fmt_get_stop_strings(formatter: LmFormatter) -> list[str]:
    match formatter:
        case GoalFormatter():
            return GoalFormatter.STOP_STRINGS
        case _:
            return []
