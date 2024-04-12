from __future__ import annotations
from typing import Any, Optional
import time
import datetime
import random
import functools
import os
import ipdb
import heapq
from dataclasses import dataclass

from data_management.splits import FileInfo
from data_management.dataset_file import DatasetFile, FocusedStep, Proof, Sentence, Goal
from tactic_gen.n_step_sampler import (
    NStepSampler,
    NStepConf,
    n_step_conf_from_yaml,
    n_step_from_conf,
)
from model_deployment.premise_client import (
    PremiseClient,
    PremiseConf,
    premise_conf_from_yaml,
    premise_client_from_conf,
)
from model_deployment.mine_goals import FileGoals, GoalRecord
from model_deployment.transform_ast import AdjTree


GOAL_SEP = "<G>"
PREM_SEP = "<P>"
PROOF_RET_SEP = "<F>"
STMT_SEP = "<S>"
THM_SEP = "<T>"
END_TOK = "<E>"
N_TAC_TOK = "<N>"


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


@dataclass
class BasicFormatterConf:
    ALIAS = "basic"
    n_step_conf: NStepConf

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> BasicFormatterConf:
        n_step_conf = n_step_conf_from_yaml(yaml_data["n_step_sampler"])
        return cls(n_step_conf)


@dataclass
class ProofRetrievalFormatterConf:
    ALIAS = "proof"
    proof_bank_loc: str
    n_step_conf: NStepConf

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> ProofRetrievalFormatterConf:
        return cls(
            yaml_data["proof_bank_loc"],
            n_step_conf_from_yaml(yaml_data["n_step_sampler"]),
        )


@dataclass
class PremiseFormatterConf:
    ALIAS = "premise"
    premise_conf: PremiseConf
    n_step_conf: NStepConf

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> PremiseFormatterConf:
        return cls(
            premise_conf_from_yaml(yaml_data["premise_conf"]),
            n_step_conf_from_yaml(yaml_data["n_step_sampler"]),
        )


FormatterConf = BasicFormatterConf | ProofRetrievalFormatterConf | PremiseFormatterConf


def formatter_conf_from_yaml(yaml_data: Any) -> FormatterConf:
    attempted_alias = yaml_data["alias"]
    match attempted_alias:
        case BasicFormatterConf.ALIAS:
            return BasicFormatterConf.from_yaml(yaml_data)
        case ProofRetrievalFormatterConf.ALIAS:
            return ProofRetrievalFormatterConf.from_yaml(yaml_data)
        case PremiseFormatterConf.ALIAS:
            return PremiseFormatterConf.from_yaml(yaml_data)
        case _:
            raise ValueError("Formatter conf not found: " + attempted_alias)


def formatter_from_conf(conf: FormatterConf) -> LmFormatter:
    match conf:
        case BasicFormatterConf():
            return BasicFormatter.from_conf(conf)
        case ProofRetrievalFormatterConf():
            return ProofRetrievalFormatter.from_conf(conf)
        case PremiseFormatterConf():
            return PremiseFormatter.from_conf(conf)


class BasicFormatter:
    def __init__(self, n_step_sampler: NStepSampler) -> None:
        self.n_step_sampler = n_step_sampler

    def example_from_step(
        self,
        step_idx: int,
        proof: Proof,
        **kwargs: Any,
    ) -> LmExample:
        step = proof.steps[step_idx]
        partial_proof_string = proof.proof_prefix_to_string(step)
        final_goal_string = fmt_goals(step.goals)
        input = f"{partial_proof_string}{THM_SEP}{final_goal_string}"
        n_step_sample = self.n_step_sampler.sample_steps(proof.steps[step_idx:])
        output = "".join([fs.step.text for fs in n_step_sample.steps])
        return LmExample(input, output)

    @classmethod
    def from_conf(cls, conf: BasicFormatterConf) -> BasicFormatter:
        return cls(n_step_from_conf(conf.n_step_conf))


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


class ProofRetrievalFormatter:
    MAX_N_EXAMPLES = 20

    def __init__(
        self,
        proof_bank_loc: str,
        n_step_sampler: NStepSampler,
    ) -> None:
        self.proof_bank_loc = proof_bank_loc
        self.n_step_sampler = n_step_sampler
        self.basic_formatter = BasicFormatter(self.n_step_sampler)

    @functools.lru_cache()
    def __get_file_goals(self, key: str) -> Optional[FileGoals]:
        goal_loc = os.path.join(self.proof_bank_loc, key)
        if not os.path.exists(goal_loc):
            return None
        goals = FileGoals.load(goal_loc)
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
            if self.MAX_N_EXAMPLES < len(best_record_candiates):
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
    def from_conf(cls, conf: ProofRetrievalFormatterConf) -> ProofRetrievalFormatter:
        return cls(
            conf.proof_bank_loc,
            n_step_from_conf(conf.n_step_conf),
        )


class PremiseFormatter:
    MAX_N_EXAMPLES = 20

    def __init__(
        self,
        premise_client: PremiseClient,
        n_step_sampler: NStepSampler,
    ) -> None:
        self.premise_client = premise_client
        self.n_step_sampler = n_step_sampler
        self.__basic_formatter = BasicFormatter(self.n_step_sampler)

    def get_premises(
        self,
        step: FocusedStep,
        proof: Proof,
        dp_obj: DatasetFile,
    ) -> list[str]:
        filtered_result = self.premise_client.premise_filter.get_pos_and_avail_premises(
            step, proof, dp_obj
        )
        ranked_premises = self.premise_client.get_ranked_premise_generator(
            step, proof, filtered_result.avail_premises
        )
        top_premises: list[Sentence] = []
        for premise in ranked_premises:
            if len(top_premises) >= self.MAX_N_EXAMPLES:
                break
            top_premises.append(premise)

        premise_strs: list[str] = []
        for premise in top_premises:
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
    def from_conf(cls, conf: PremiseFormatterConf) -> PremiseFormatter:
        return cls(
            premise_client_from_conf(conf.premise_conf),
            n_step_from_conf(conf.n_step_conf),
        )


LmFormatter = BasicFormatter | PremiseFormatter | ProofRetrievalFormatter
