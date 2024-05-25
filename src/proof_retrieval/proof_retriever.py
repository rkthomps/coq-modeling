from __future__ import annotations
from typing import Any, Optional
import functools
from dataclasses import dataclass

import os
import random
import heapq
from pathlib import Path

from data_management.sentence_db import SentenceDB
from data_management.splits import FileInfo
from data_management.dataset_file import (
    FocusedStep,
    Proof,
    DatasetFile,
    DPCache,
    Goal,
    get_ids_from_goal,
    get_ids_from_sentence,
)
from proof_retrieval.tfidf import tf_idf
from proof_retrieval.mine_goals import FileGoals, GoalRecord
from proof_retrieval.transform_ast import AdjTree


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


@dataclass
class TextProofRetrieverConf:
    max_examples: int
    data_loc: Path
    sentence_db_loc: Path

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> TextProofRetrieverConf:
        return cls(
            yaml_data["max_examples"],
            Path(yaml_data["data_loc"]),
            Path(yaml_data["sentence_db_loc"]),
        )


class TextProofRetriever:
    def __init__(
        self, max_examples: int, data_loc: Path, sentence_db: SentenceDB
    ) -> None:
        self.max_examples = max_examples
        self.data_loc = data_loc
        self.sentence_db = sentence_db
        self.dp_cache = DPCache()

    def get_available_proofs(
        self, key_proof: Proof, dp_obj: DatasetFile
    ) -> list[Proof]:
        available_proofs: list[Proof] = []
        for proof in dp_obj.proofs:
            if proof == key_proof:
                break
            available_proofs.append(proof)

        print("Dependencies", dp_obj.dependencies)
        for dep in dp_obj.dependencies:
            try:
                dep_obj = self.dp_cache.get_dp(dep, self.data_loc, self.sentence_db)
            except FileNotFoundError:
                print("Could not find dependency: ", dep)
                continue
            for proof in dep_obj.proofs:
                available_proofs.append(proof)
        return available_proofs

    def get_goal_ids(self, goals: list[Goal]) -> list[str]:
        ids: list[str] = []
        for g in goals:
            hyp_ids, goal_ids = get_ids_from_goal(g)
            ids.extend(hyp_ids)
            ids.extend(goal_ids)
        return ids

    def get_similar_proofs(
        self, key_step: FocusedStep, key_proof: Proof, dp_obj: DatasetFile
    ) -> list[Proof]:
        if len(key_step.goals) == 0:
            return []
        query_ids = self.get_goal_ids(key_step.goals)
        available_proofs = self.get_available_proofs(key_proof, dp_obj)
        reference_proofs: list[Proof] = []
        docs: list[list[str]] = []
        for ref_proof in available_proofs:
            for step in ref_proof.steps:
                reference_proofs.append(ref_proof)
                docs.append(self.get_goal_ids(step.goals))
        assert len(docs) == len(reference_proofs)
        scores = tf_idf(query_ids, docs)
        arg_sorted_scores = sorted(range(len(scores)), key=lambda idx: -1 * scores[idx])
        similar_proofs: list[Proof] = []
        for proof_idx in arg_sorted_scores:
            if self.max_examples <= len(similar_proofs):
                continue
            similar_proof = reference_proofs[proof_idx]
            if similar_proof in similar_proofs:
                continue
            similar_proofs.append(similar_proof)
        return similar_proofs

    def close(self):
        self.sentence_db.close()

    @classmethod
    def from_conf(cls, conf: TextProofRetrieverConf) -> TextProofRetriever:
        return cls(
            conf.max_examples,
            conf.data_loc,
            SentenceDB.load(conf.sentence_db_loc),
        )
