from __future__ import annotations
from typing import Any, Optional
import time
import datetime
import random
import os
import ipdb
import heapq

from dataclasses import dataclass
from typeguard import typechecked
from transformers import CodeLlamaTokenizer

from data_management.splits import FileInfo, Split
from data_management.dataset_file import DatasetFile, FocusedStep, Proof, Sentence, Goal
from tactic_gen.proof_distance import SortedProofs, StrippedProof
from tactic_gen.n_step_sampler import NStepSampler, OneStepSampler, n_step_from_conf
from tactic_gen.step_parser import norm, CoqParseError
from model_deployment.premise_client import PremiseClient
from model_deployment.mine_goals import FileGoals, GoalRecord
from model_deployment.transform_ast import AdjTree
from util.util import get_basic_logger

from coqpyt.coq.structs import TermType

_logger = get_basic_logger(__name__)

GOAL_SEP = "<G>"
PREM_SEP = "<P>"
PROOF_RET_SEP = "<F>"
STMT_SEP = "<S>"
THM_SEP = "<T>"
END_TOK = "<E>"
N_TAC_TOK = "<N>"


class LmExample:
    def __init__(
        self, input: str, output: str, passages: Optional[list[str]] = None
    ) -> None:
        self.input = input
        self.output = output
        self.passages = passages

    def to_json(self) -> Any:
        return {
            "input": self.input,
            "output": self.output,
            "passages": self.passages,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> LmExample:
        passages = json_data["passages"] if "passages" in json_data else None
        return cls(json_data["input"], json_data["output"], passages)


def fmt_goals(goals: list[Goal]) -> str:
    goal_strings = [goal.to_string() for goal in goals]
    return GOAL_SEP.join(goal_strings)


class BasicWholeProofFormatter:
    ALIAS = "basic-whole-proof"

    def __init__(self, conf: Any):
        self.conf = conf

    def example_from_proof(self, proof: Proof) -> LmExample:
        theorem_text = proof.theorem.term.text
        proof_text = proof.proof_text_to_string(include_theorem=False)
        return LmExample(theorem_text, proof_text)


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
        **kwargs: Any,
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


def allocate_tokens(
    tokenizer: CodeLlamaTokenizer, s: str, allowance: int, truncate_front=True
) -> tuple[str, int]:
    tokens = tokenizer.encode(s)
    if truncate_front:
        to_add = tokens[(-1 * allowance) :]
    else:
        to_add = tokens[:allowance]
    return tokenizer.decode(to_add, skip_special_tokens=True), len(to_add)


class ProofCandidate:
    def __init__(self, distance: int, candidate: GoalRecord):
        self.distance = distance
        self.candidate = candidate

    def __lt__(self, other: ProofCandidate) -> bool:
        return self.distance < other.distance

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, ProofCandidate):
            return False
        return self.distance == other.distance


class ProofCandidateReversed(ProofCandidate):
    def __init__(self, distance: int, candidate: GoalRecord):
        super(ProofCandidateReversed, self).__init__(distance, candidate)

    def __lt__(self, other: ProofCandidate) -> bool:
        return other.distance < self.distance


class ProofRetrievalFidFormatter:
    ALIAS = "proof-ret-fid"

    def __init__(
        self,
        proof_bank_loc: str,
        n_proofs: int,
        n_step_sampler: NStepSampler,
        direct_num_steps: bool,
        conf: Any,
    ) -> None:
        self.proof_bank_loc = proof_bank_loc
        self.n_proofs = n_proofs
        self.__proof_bank: dict[str, FileGoals] = {}
        self.n_step_sampler = n_step_sampler
        self.direct_num_steps = direct_num_steps
        self.conf = conf
        self.basic_formatter = BasicFormatter(
            self.n_step_sampler, self.direct_num_steps, conf
        )

    def __get_file_goals(self, key: str) -> Optional[FileGoals]:
        if key in self.__proof_bank:
            return self.__proof_bank[key]
        goal_loc = os.path.join(self.proof_bank_loc, key)
        if not os.path.exists(goal_loc):
            return None
        goals = FileGoals.load(goal_loc)
        self.__proof_bank[key] = goals
        return goals

    def get_record_and_cutoff_index(
        self, step_idx: int, proof: Proof, file_goals: FileGoals
    ) -> Optional[tuple[int, int]]:
        current_ground_truth = [s.step.text for s in proof.steps[step_idx:]]
        complete_ground_truth = [s.step.text for s in proof.steps]
        record_idx: Optional[int] = None
        cur_ground_truth_str = "".join(current_ground_truth)
        if len(proof.steps[step_idx].goals) <= 0:
            return None
        pretty_proof_goal = proof.steps[step_idx].goals[0].to_string().strip()
        for i, record in enumerate(file_goals.records):
            record_proof_str = "".join(record.proof)
            if record.pretty_goal.strip() == pretty_proof_goal and (
                cur_ground_truth_str.startswith(record_proof_str)
                or record_proof_str.startswith(cur_ground_truth_str)
            ):
                record_idx = i
                break
        if record_idx is None:
            return None

        prefix_len = len(complete_ground_truth) - len(current_ground_truth)
        current_record = file_goals.records[record_idx]
        proof_start_idx = current_record.step_idx - prefix_len
        return record_idx, proof_start_idx

    def get_in_file_candidates(
        self, cutoff_idx: int, file_goals: Optional[FileGoals]
    ) -> list[GoalRecord]:
        if file_goals is None:
            return []
        candidate_records: list[GoalRecord] = []
        for record in file_goals.records:
            if cutoff_idx <= record.step_idx:
                break
            candidate_records.append(record)
        return candidate_records

    def get_out_of_file_candidates(self, dp_obj: DatasetFile):
        candidates: list[GoalRecord] = []
        for dependency in dp_obj.dependencies:
            dependency_goals = self.__get_file_goals(dependency)
            if dependency_goals is None:
                continue
            for record in dependency_goals.records:
                candidates.append(record)
        return candidates

    def get_similar_proofs(
        self,
        step_idx: int,
        proof: Proof,
        dp_obj: DatasetFile,
        file_info: FileInfo,
        key_record: Optional[GoalRecord] = None,
        cutoff_idx: Optional[int] = None,
        max_num_nodes: int = 30,
        max_num_steps: int = 500,
    ) -> list[GoalRecord]:
        file_goals = self.__get_file_goals(file_info.dp_name)
        if key_record is None and cutoff_idx is None:
            if file_goals is None:
                return []
            record_result = self.get_record_and_cutoff_index(
                step_idx, proof, file_goals
            )
            if record_result is None:
                return []
            record_idx, cutoff_idx = record_result
            key_record = file_goals.records[record_idx]
        elif key_record is None or cutoff_idx is None:
            return []

        in_file_candidates = self.get_in_file_candidates(cutoff_idx, file_goals)
        in_file_candidates.reverse()
        out_of_file_candidates = self.get_out_of_file_candidates(dp_obj)
        all_raw_candidates = in_file_candidates + out_of_file_candidates
        key_prefix = key_record.term.get_breadth_prefix(max_num_nodes)
        key_adjtree = AdjTree.from_stree(key_prefix)

        best_record_candiates: list[ProofCandidateReversed] = []
        if max_num_steps < len(all_raw_candidates):
            selected_raw_candidates = random.sample(all_raw_candidates, max_num_steps)
        else:
            selected_raw_candidates = all_raw_candidates

        for c in selected_raw_candidates:
            c_prefix = c.term.get_breadth_prefix(max_num_nodes)
            c_adjtree = AdjTree.from_stree(c_prefix)
            c_distance = key_adjtree.distance(c_adjtree)
            heapq.heappush(best_record_candiates, ProofCandidateReversed(c_distance, c))
            if self.n_proofs < len(best_record_candiates):
                heapq.heappop(best_record_candiates)
        sorted_candidates = heapq.nlargest(
            len(best_record_candiates), best_record_candiates
        )
        return [c.candidate for c in sorted_candidates]

    def example_from_step(
        self,
        step_idx: int,
        proof: Proof,
        dp_obj: DatasetFile,
        file_info: FileInfo,
        key_record: Optional[GoalRecord] = None,
        cutoff_idx: Optional[int] = None,
        **kwargs: Any,
    ) -> LmExample:
        similar_proof_result = self.get_similar_proofs(
            step_idx, proof, dp_obj, file_info, key_record, cutoff_idx
        )
        passages: list[str] = []
        for record in similar_proof_result:
            passages.append(
                f"{record.pretty_goal}{PROOF_RET_SEP}{''.join(record.proof)}"
            )

        basic_example = self.basic_formatter.example_from_step(step_idx, proof)
        return LmExample(basic_example.input, basic_example.output, passages)

    @classmethod
    def from_conf(cls, conf: Any) -> ProofRetrievalFidFormatter:
        proof_bank_loc = conf["proof_bank_loc"]
        n_proofs = conf["n_proofs"]
        tmp_basic_formatter = BasicFormatter.from_conf(conf)
        return cls(
            proof_bank_loc,
            n_proofs,
            tmp_basic_formatter.n_step_sampler,
            tmp_basic_formatter.direct_num_steps,
            conf,
        )


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
        self.sub_formatter = ProofRetrievalFidFormatter(
            proof_bank_loc, 1, n_step_sampler, direct_num_steps, conf
        )
        self.tokenizer = tokenizer
        self.state_num_tokens = state_num_tokens
        self.script_num_tokens = script_num_tokens
        self.statement_num_tokens = statement_num_tokens
        self.ret_proof_state_tokens = ret_proof_state_tokens
        self.ret_proof_script_tokens = ret_proof_script_tokens
        self.n_step_sampler = n_step_sampler
        self.direct_num_steps = direct_num_steps
        self.conf = conf

    def example_from_step(
        self,
        step_idx: int,
        proof: Proof,
        dp_obj: DatasetFile,
        file_info: FileInfo,
        key_record: Optional[GoalRecord] = None,
        cutoff_idx: Optional[int] = None,
        **kwargs: Any,
    ) -> LmExample:
        step = proof.steps[step_idx]
        similar_proof_result = self.sub_formatter.get_similar_proofs(
            step_idx, proof, dp_obj, file_info, key_record, cutoff_idx
        )
        if 0 < len(similar_proof_result):
            similar_proof_record = similar_proof_result[0]
            similar_proof_state, similar_proof_script = (
                similar_proof_record.pretty_goal,
                similar_proof_record.proof,
            )
            ret_state_str, _ = allocate_tokens(
                self.tokenizer, similar_proof_state, self.ret_proof_state_tokens
            )
            ret_script_str, _ = allocate_tokens(
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

    @classmethod
    def from_conf(cls, conf: Any) -> ProofRetrievalFormatter:
        proof_bank_loc = conf["proof_bank_loc"]
        model_name = conf["model_name"]
        tokenizer = CodeLlamaTokenizer.from_pretrained(model_name, use_fast=True)
        state_num_tokens = conf["state_num_tokens"]
        script_num_tokens = conf["script_num_tokens"]
        statement_num_tokens = conf["statement_num_tokens"]
        ret_proof_state_tokens = conf["ret_proof_state_tokens"]
        ret_proof_script_tokens = conf["ret_proof_script_tokens"]
        tmp_basic_formatter = BasicFormatter.from_conf(conf)
        return cls(
            proof_bank_loc,
            tokenizer,
            state_num_tokens,
            script_num_tokens,
            statement_num_tokens,
            ret_proof_state_tokens,
            ret_proof_script_tokens,
            tmp_basic_formatter.n_step_sampler,
            tmp_basic_formatter.direct_num_steps,
            conf,
        )


class FidPremiseFormatter:
    ALIAS = "fid-premise"
    REQUIRES_GPU = True
    MAX_N_EXAMPLES = 20

    def __init__(
        self,
        premise_client: PremiseClient,
        n_step_sampler: NStepSampler,
        direct_num_steps: bool,
        conf: Any,
    ) -> None:
        self.premise_client = premise_client
        self.n_step_sampler = n_step_sampler
        self.direct_num_steps = direct_num_steps
        self.__basic_formatter = BasicFormatter(
            self.n_step_sampler, self.direct_num_steps, conf
        )
        self.conf = conf

    def get_premises(
        self,
        step: FocusedStep,
        proof: Proof,
        dp_obj: DatasetFile,
    ) -> list[str]:
        filtered_result = self.premise_client.premise_filter.get_pos_and_avail_premises(
            step, proof, dp_obj
        )
        ranked_premises = get_ranked_premise_generator(
            self.premise_client, step, proof, filtered_result.avail_premises
        )
        top_premises: list[Sentence] = []
        for premise in ranked_premises:
            if len(top_premises) >= self.MAX_N_EXAMPLES:
                break
            top_premises.append(premise)

        premise_strs: list[str] = []
        for i, premise in enumerate(top_premises):
            premise_strs.append(f"{premise.text}")

        return premise_strs

    def example_from_step(
        self,
        step_idx: int,
        proof: Proof,
        dp_obj: DatasetFile,
        **kwargs: Any,
    ) -> LmExample:
        step = proof.steps[step_idx]
        premise_strs = self.get_premises(step, proof, dp_obj)
        basic_lm_example = self.__basic_formatter.example_from_step(step_idx, proof)
        return LmExample(basic_lm_example.input, basic_lm_example.output, premise_strs)

    @classmethod
    def from_conf(cls, conf: Any) -> FidPremiseFormatter:
        premise_model_wrapper = premise_wrapper_from_conf(conf["premise_model_wrapper"])
        tmp_basic_formatter = BasicFormatter.from_conf(conf)
        return cls(
            premise_model_wrapper,
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
        **kwargs: Any,
    ) -> LmExample:
        step = proof.steps[step_idx]
        premise_str = self.get_premise_str(step, proof, dp_obj)
        basic_lm_example = self.__basic_formatter.example_from_step(
            step_idx,
            proof,
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


class LmFormatterNotFoundError(Exception):
    pass


LmFormatter = (
    BasicFormatter
    | FidPremiseFormatter
    | PremiseFormatter
    | ProofRetrievalFormatter
    | ProofRetrievalFidFormatter
)


def fmt_from_conf(conf: Any) -> LmFormatter:
    attempted_alias = conf["alias"]
    match attempted_alias:
        case BasicFormatter.ALIAS:
            return BasicFormatter.from_conf(conf)
        case PremiseFormatter.ALIAS:
            return PremiseFormatter.from_conf(conf)
        case FidPremiseFormatter.ALIAS:
            return FidPremiseFormatter.from_conf(conf)
        case ProofRetrievalFormatter.ALIAS:
            return ProofRetrievalFormatter.from_conf(conf)
        case ProofRetrievalFidFormatter.ALIAS:
            return ProofRetrievalFidFormatter.from_conf(conf)
        case _:
            raise LmFormatterNotFoundError(
                f'Could not find Lm Formatter: "{attempted_alias}"'
            )
