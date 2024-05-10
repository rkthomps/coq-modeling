from __future__ import annotations
from typing import Any, Optional
import random
import functools
import ipdb
import os
import heapq
from pathlib import Path
from dataclasses import dataclass

from data_management.splits import FileInfo
from data_management.dataset_file import (
    DatasetFile,
    DPCache,
    FocusedStep,
    Proof,
    Sentence,
    Goal,
)
from tactic_gen.n_step_sampler import (
    NStepSampler,
    NStepConf,
    n_step_conf_from_yaml,
    n_step_from_conf,
)
from premise_selection.premise_filter import PremiseFilter, NO_COQ_LEMMA_FILTER
from model_deployment.premise_client import (
    PremiseClient,
    PremiseConf,
    premise_conf_from_yaml,
    premise_client_from_conf,
    merge_premise_confs,
)
from model_deployment.mine_goals import FileGoals, GoalRecord
from model_deployment.transform_ast import AdjTree
from data_management.sentence_db import SentenceDB
from data_management.splits import DATA_POINTS_NAME
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
class ProofLastFormatterConf:
    ALIAS = "proof-last"
    n_step_conf: NStepConf

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> ProofLastFormatterConf:
        n_step_conf = n_step_conf_from_yaml(yaml_data["n_step_sampler"])
        return cls(n_step_conf)


@dataclass
class ProofRetrievalFormatterConf:
    ALIAS = "proof"
    proof_bank_loc: Path
    n_step_conf: NStepConf

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> ProofRetrievalFormatterConf:
        return cls(
            Path(yaml_data["proof_bank_loc"]),
            n_step_conf_from_yaml(yaml_data["n_step_sampler"]),
        )


@dataclass
class WholeProofRetrievalFormatterConf:
    ALIAS = "whole-proof-ret"
    proof_bank_loc: Path
    data_loc: Path
    sentence_db_loc: Path
    n_step_conf: NStepConf

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> WholeProofRetrievalFormatterConf:
        return cls(
            Path(yaml_data["proof_bank_loc"]),
            Path(yaml_data["data_loc"]),
            Path(yaml_data["sentence_db_loc"]),
            n_step_conf_from_yaml(yaml_data["n_step_sampler"]),
        )


@dataclass
class WholeProofPremiseRetrievalFormatterConf:
    ALIAS = "whole-proof-ret-premise"
    proof_bank_loc: Path
    data_loc: Path
    sentence_db_loc: Path
    n_step_conf: NStepConf

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> WholeProofPremiseRetrievalFormatterConf:
        return cls(
            Path(yaml_data["proof_bank_loc"]),
            Path(yaml_data["data_loc"]),
            Path(yaml_data["sentence_db_loc"]),
            n_step_conf_from_yaml(yaml_data["n_step_sampler"]),
        )


@dataclass
class PremiseFormatterConf:
    ALIAS = "premise"
    premise_conf: PremiseConf
    n_step_conf: NStepConf

    def merge(self, other: PremiseFormatterConf) -> PremiseFormatterConf:
        assert self.n_step_conf == other.n_step_conf
        new_premise_conf = merge_premise_confs(self.premise_conf, other.premise_conf)
        return PremiseFormatterConf(new_premise_conf, self.n_step_conf)

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> PremiseFormatterConf:
        return cls(
            premise_conf_from_yaml(yaml_data["premise_conf"]),
            n_step_conf_from_yaml(yaml_data["n_step_sampler"]),
        )


@dataclass
class GPTVanillaFormatterConf:
    ALIAS = "gpt-vanilla"

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> GPTVanillaFormatterConf:
        return cls()


@dataclass
class GPTProofFormatterConf:
    ALIAS = "gpt-proof"
    proof_bank_loc: Path
    data_loc: Path
    sentence_db_loc: Path

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> GPTProofFormatterConf:
        return cls(
            Path(yaml_data["proof_bank_loc"]),
            Path(yaml_data["data_loc"]),
            Path(yaml_data["sentence_db_loc"]),
        )


@dataclass
class GPTPremiseFormatterConf:
    ALIAS = "gpt-premise"
    premise_conf: PremiseConf

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> GPTPremiseFormatterConf:
        return cls(premise_conf_from_yaml(yaml_data["premise_conf"]))


GPTFormatterConf = GPTVanillaFormatterConf
FormatterConf = (
    BasicFormatterConf
    | ProofLastFormatterConf
    | ProofRetrievalFormatterConf
    | WholeProofRetrievalFormatterConf
    | WholeProofPremiseRetrievalFormatterConf
    | PremiseFormatterConf
    | GPTVanillaFormatterConf
    | GPTProofFormatterConf
    | GPTPremiseFormatterConf
)


def merge_formatters(f1: FormatterConf, f2: FormatterConf) -> FormatterConf:
    match f1:
        case PremiseFormatterConf():
            assert isinstance(f2, PremiseFormatterConf)
            return f1.merge(f2)
        case _:
            assert f1 == f2
            return f1


def formatter_conf_from_yaml(yaml_data: Any) -> FormatterConf:
    attempted_alias = yaml_data["alias"]
    match attempted_alias:
        case BasicFormatterConf.ALIAS:
            return BasicFormatterConf.from_yaml(yaml_data)
        case ProofLastFormatterConf.ALIAS:
            return ProofLastFormatterConf.from_yaml(yaml_data)
        case ProofRetrievalFormatterConf.ALIAS:
            return ProofRetrievalFormatterConf.from_yaml(yaml_data)
        case WholeProofRetrievalFormatterConf.ALIAS:
            return WholeProofRetrievalFormatterConf.from_yaml(yaml_data)
        case WholeProofPremiseRetrievalFormatterConf.ALIAS:
            return WholeProofPremiseRetrievalFormatterConf.from_yaml(yaml_data)
        case PremiseFormatterConf.ALIAS:
            return PremiseFormatterConf.from_yaml(yaml_data)
        case GPTVanillaFormatterConf.ALIAS:
            return GPTVanillaFormatterConf.from_yaml(yaml_data)
        case GPTProofFormatterConf.ALIAS:
            return GPTProofFormatterConf.from_yaml(yaml_data)
        case GPTPremiseFormatterConf.ALIAS:
            return GPTPremiseFormatterConf.from_yaml(yaml_data)
        case _:
            raise ValueError("Formatter conf not found: " + attempted_alias)


def formatter_from_conf(conf: FormatterConf) -> LmFormatter:
    match conf:
        case BasicFormatterConf():
            return BasicFormatter.from_conf(conf)
        case ProofLastFormatterConf():
            return ProofLastFormatter.from_conf(conf)
        case ProofRetrievalFormatterConf():
            return ProofRetrievalFormatter.from_conf(conf)
        case WholeProofRetrievalFormatterConf():
            return WholeProofRetrievalFormatter.from_conf(conf)
        case WholeProofPremiseRetrievalFormatterConf():
            return WholeProofPremiseRetrievalFormatter.from_conf(conf)
        case PremiseFormatterConf():
            return PremiseFormatter.from_conf(conf)
        case GPTVanillaFormatterConf():
            return GPTVanillaFormatter.from_conf(conf)
        case GPTProofFormatterConf():
            return GPTProofFormatter.from_conf(conf)
        case GPTPremiseFormatterConf():
            return GPTPremiseFormatter.from_conf(conf)


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


class ProofLastFormatter:
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
        input = f"{final_goal_string}{THM_SEP}{partial_proof_string}"
        n_step_sample = self.n_step_sampler.sample_steps(proof.steps[step_idx:])
        output = "".join([fs.step.text for fs in n_step_sample.steps])
        return LmExample(input, output)

    @classmethod
    def from_conf(cls, conf: ProofLastFormatterConf) -> ProofLastFormatter:
        return cls(n_step_from_conf(conf.n_step_conf))


class ProofCandidate:
    def __init__(self, distance: int, candidate: GoalRecord, origin: str):
        self.distance = distance
        self.candidate = candidate
        self.origin = origin

    def __lt__(self, other: ProofCandidate) -> bool:
        return self.distance < other.distance

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, ProofCandidate):
            return False
        return self.distance == other.distance


class ProofCandidateReversed(ProofCandidate):
    def __init__(self, distance: int, candidate: GoalRecord, origin: str):
        super(ProofCandidateReversed, self).__init__(distance, candidate, origin)

    def __lt__(self, other: ProofCandidate) -> bool:
        return other.distance < self.distance


class ProofRetriever:
    def __init__(self, proof_bank_loc: Path, max_examples: int):
        self.proof_bank_loc = proof_bank_loc
        self.max_examples = max_examples
        self.dp_cache = DPCache()

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
        norm_pretty_proof_goal = " ".join(
            proof.steps[step_idx].goals[0].to_string().split()
        )
        for i, record in enumerate(file_goals.records):
            record_proof_str = "".join(record.proof)
            norm_record_goal = " ".join(record.pretty_goal.split())
            if norm_record_goal == norm_pretty_proof_goal and (
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
        self, cutoff_idx: int, file_goals: Optional[FileGoals], file_dp_name: str
    ) -> list[tuple[GoalRecord, str]]:
        if file_goals is None:
            return []
        candidate_records: list[tuple[GoalRecord, str]] = []
        for record in file_goals.records:
            if cutoff_idx <= record.step_idx:
                break
            candidate_records.append((record, file_dp_name))
        return candidate_records

    def get_out_of_file_candidates(
        self, dp_obj: DatasetFile
    ) -> list[tuple[GoalRecord, str]]:
        candidates: list[tuple[GoalRecord, str]] = []
        for dependency in dp_obj.dependencies:
            dependency_goals = self.__get_file_goals(dependency)
            if dependency_goals is None:
                continue
            for record in dependency_goals.records:
                candidates.append((record, dependency))
        return candidates

    def get_whole_proof(
        self, candidate: ProofCandidateReversed, data_loc: Path, sentence_db: SentenceDB
    ) -> tuple[Proof, str]:
        candidate_dp = self.dp_cache.get_dp(candidate.origin, data_loc, sentence_db)
        record_proof_str = " ".join("".join(candidate.candidate.proof).split())
        pretty_candidate_goal = " ".join(candidate.candidate.pretty_goal.split())
        for proof in candidate_dp.proofs:
            for i, step in enumerate(proof.steps):
                if 0 == len(step.goals):
                    continue
                current_ground_truth = [s.step.text for s in proof.steps[i:]]
                cur_ground_truth_str = " ".join("".join(current_ground_truth).split())
                pretty_proof_goal = " ".join(step.goals[0].to_string().split())
                if pretty_candidate_goal == pretty_proof_goal and (
                    cur_ground_truth_str.startswith(record_proof_str)
                    or record_proof_str.startswith(cur_ground_truth_str)
                ):
                    return proof, candidate.origin
        print(candidate.candidate.pretty_goal)
        raise ValueError(
            "Could not find corresponding candidate's corresponding proof."
        )

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
    ) -> list[ProofCandidateReversed]:
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

        in_file_candidates = self.get_in_file_candidates(
            cutoff_idx, file_goals, file_info.dp_name
        )
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

        for c, o in selected_raw_candidates:
            c_prefix = c.term.get_breadth_prefix(max_num_nodes)
            c_adjtree = AdjTree.from_stree(c_prefix)
            c_distance = key_adjtree.distance(c_adjtree)
            heapq.heappush(
                best_record_candiates, ProofCandidateReversed(c_distance, c, o)
            )
            if self.max_examples < len(best_record_candiates):
                heapq.heappop(best_record_candiates)
        sorted_candidates = heapq.nlargest(
            len(best_record_candiates), best_record_candiates
        )
        return sorted_candidates


class WholeProofRetrievalFormatter:
    MAX_N_EXAMPLES = 20

    def __init__(
        self,
        proof_retriever: ProofRetriever,
        data_loc: Path,
        sentence_db: SentenceDB,
        n_step_sampler: NStepSampler,
    ) -> None:
        self.proof_retriever = proof_retriever
        self.data_loc = data_loc
        self.sentence_db = sentence_db
        self.n_step_sampler = n_step_sampler
        self.basic_formatter = BasicFormatter(self.n_step_sampler)

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
        similar_proof_result = self.proof_retriever.get_similar_proofs(
            step_idx, proof, dp_obj, file_info, key_record, cutoff_idx
        )
        similar_whole_proofs: dict[tuple[str, str], Proof] = {}
        for r in similar_proof_result:
            try:
                proof_obj, origin = self.proof_retriever.get_whole_proof(
                    r, self.data_loc, self.sentence_db
                )
                proof_str = proof_obj.proof_text_to_string()
                key = (proof_str, origin)
                if key in similar_whole_proofs:
                    continue
                if self.MAX_N_EXAMPLES <= len(similar_whole_proofs):
                    break
                similar_whole_proofs[key] = proof_obj
            except ValueError:
                _logger.warning(f"Couldn't find corresponding proof with {r.origin}")

        passages = [s for s, _ in similar_whole_proofs]
        basic_example = self.basic_formatter.example_from_step(step_idx, proof)
        return LmExample(basic_example.input, basic_example.output, passages)

    @classmethod
    def from_conf(
        cls, conf: WholeProofRetrievalFormatterConf
    ) -> WholeProofRetrievalFormatter:
        sentence_db = SentenceDB.load(conf.sentence_db_loc)
        return cls(
            ProofRetriever(conf.proof_bank_loc, cls.MAX_N_EXAMPLES),
            conf.data_loc,
            sentence_db,
            n_step_from_conf(conf.n_step_conf),
        )


def premises_from_proof(proof: Proof, premise_filter: PremiseFilter) -> list[Sentence]:
    gathered_premises: list[Sentence] = []
    for step in proof.steps:
        for premise in step.step.context:
            if not premise_filter.filter_premise(premise):
                continue
            if premise in gathered_premises:
                continue
            gathered_premises.append(premise)
    return gathered_premises


class WholeProofPremiseRetrievalFormatter:
    MAX_N_EXAMPLES = 20
    PREMISE_FILTER = NO_COQ_LEMMA_FILTER

    def __init__(
        self,
        proof_retriever: ProofRetriever,
        data_loc: Path,
        sentence_db: SentenceDB,
        n_step_sampler: NStepSampler,
    ):
        self.proof_retriever = proof_retriever
        self.data_loc = data_loc
        self.sentence_db = sentence_db
        self.n_step_sampler = n_step_sampler
        self.basic_formatter = BasicFormatter(self.n_step_sampler)

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
        similar_proof_result = self.proof_retriever.get_similar_proofs(
            step_idx, proof, dp_obj, file_info, key_record, cutoff_idx
        )
        seen_whole_proofs: set[tuple[str, str]] = set()
        similar_whole_proofs: list[Proof] = []
        for r in similar_proof_result:
            try:
                proof_obj, origin = self.proof_retriever.get_whole_proof(
                    r, self.data_loc, self.sentence_db
                )
                proof_str = proof_obj.proof_text_to_string()
                key = (proof_str, origin)
                if key in seen_whole_proofs:
                    continue
                if self.MAX_N_EXAMPLES <= len(similar_whole_proofs):
                    break
                seen_whole_proofs.add(key)
                similar_whole_proofs.append(proof_obj)
            except ValueError:
                _logger.warning(f"Couldn't find corresponding proof with {r.origin}")

        passages: list[str] = []
        for p in similar_whole_proofs:
            proof_premises = premises_from_proof(p, self.PREMISE_FILTER)
            premise_str = "\n".join([s.text for s in proof_premises])
            passages.append(f"{p.proof_text_to_string()}\n{premise_str}")

        basic_example = self.basic_formatter.example_from_step(step_idx, proof)
        return LmExample(basic_example.input, basic_example.output, passages)

    @classmethod
    def from_conf(
        cls,
        conf: WholeProofPremiseRetrievalFormatterConf,
    ) -> WholeProofPremiseRetrievalFormatter:
        sentence_db = SentenceDB.load(conf.sentence_db_loc)
        return cls(
            ProofRetriever(conf.proof_bank_loc, cls.MAX_N_EXAMPLES),
            conf.data_loc,
            sentence_db,
            n_step_from_conf(conf.n_step_conf),
        )


class ProofRetrievalFormatter:
    MAX_N_EXAMPLES = 20

    def __init__(
        self,
        proof_retriever: ProofRetriever,
        n_step_sampler: NStepSampler,
    ) -> None:
        self.proof_retriever = proof_retriever
        self.n_step_sampler = n_step_sampler
        self.basic_formatter = BasicFormatter(self.n_step_sampler)

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
        similar_proof_result = self.proof_retriever.get_similar_proofs(
            step_idx, proof, dp_obj, file_info, key_record, cutoff_idx
        )
        passages: list[str] = []
        for candidate in similar_proof_result:
            passages.append(
                f"{candidate.candidate.pretty_goal}{PROOF_RET_SEP}{''.join(candidate.candidate.proof)}"
            )

        basic_example = self.basic_formatter.example_from_step(step_idx, proof)
        return LmExample(basic_example.input, basic_example.output, passages)

    @classmethod
    def from_conf(cls, conf: ProofRetrievalFormatterConf) -> ProofRetrievalFormatter:
        return cls(
            ProofRetriever(conf.proof_bank_loc, cls.MAX_N_EXAMPLES),
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


class GPTVanillaFormatter:
    SYSTEM_MSG = "You complete the given proof in Coq. You continue from where the prompt left off. You only write Coq code."

    def example_from_step(
        self,
        step_idx: int,
        proof: Proof,
        dp_obj: DatasetFile,
        **kwargs: Any,
    ) -> LmExample:
        format = f"{proof.theorem.term.text}\nProof. "
        print(format)
        return LmExample(format, "out", None)

    @classmethod
    def from_conf(cls, conf: GPTVanillaFormatterConf) -> GPTVanillaFormatter:
        return cls()


@dataclass
class GPTProofFormatter:
    proof_retriever: ProofRetriever
    data_loc: Path
    sentence_db: SentenceDB
    NUM_STEPS = 8
    SYSTEM_MSG = (
        "You complete the given proof in Coq. You continue from where the prompt left off. You only write Coq code."
        "In the context, you are given proofs that at some point in the proof, solve "
        "a goal similar to the current theorem."
        "Stop after proving a single theorem. "
    )

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
        similar_proof_result = self.proof_retriever.get_similar_proofs(
            step_idx, proof, dp_obj, file_info, key_record, cutoff_idx
        )
        similar_whole_proofs: list[tuple[str, str]] = []
        for r in similar_proof_result:
            try:
                proof, origin = self.proof_retriever.get_whole_proof(
                    r, self.data_loc, self.sentence_db
                )
                key = proof.proof_text_to_string(), origin
                if key in similar_whole_proofs:
                    continue
                if self.NUM_STEPS <= len(similar_whole_proofs):
                    break
                similar_whole_proofs.append(key)
            except ValueError:
                _logger.warning(f"Couldn't find corresponding proof with {r.origin}")

        passages = [s for s, _ in similar_whole_proofs]
        similar_whole_proofs.reverse()
        print("proofs", similar_whole_proofs)
        context = "\n\n".join([p for p, _ in similar_whole_proofs])
        format = f"{context}\n\n{proof.theorem.term.text}\nProof. "
        print(format)
        return LmExample(format, "out", passages)

    @classmethod
    def from_conf(cls, conf: GPTProofFormatterConf) -> GPTProofFormatter:
        return cls(
            ProofRetriever(conf.proof_bank_loc, cls.NUM_STEPS),
            conf.data_loc,
            SentenceDB.load(conf.sentence_db_loc),
        )


@dataclass
class GPTPremiseFormatter:
    premise_client: PremiseClient
    SYSTEM_MSG = (
        "You complete the given proof in Coq. You continue from where the prompt left off. You only write Coq code."
        "In the context, you are given theorems, definitions, and notations that might be helpful "
        "for completing the proof."
    )

    def example_from_step(
        self,
        step_idx: int,
        proof: Proof,
        dp_obj: DatasetFile,
        **kwargs: Any,
    ) -> LmExample:
        format = f"{proof.theorem.term.text}\nProof. "
        return LmExample(format, "out", None)

    @classmethod
    def from_conf(cls, conf: GPTPremiseFormatterConf) -> GPTPremiseFormatter:
        return cls(premise_client_from_conf(conf.premise_conf))


GPTFormatter = GPTVanillaFormatter | GPTProofFormatter | GPTPremiseFormatter
LmFormatter = (
    BasicFormatter
    | ProofLastFormatter
    | PremiseFormatter
    | ProofRetrievalFormatter
    | WholeProofRetrievalFormatter
    | WholeProofPremiseRetrievalFormatter
    | GPTVanillaFormatter
    | GPTProofFormatter
    | GPTPremiseFormatter
)
