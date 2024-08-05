from __future__ import annotations
from typing import Any, Optional
import functools
from dataclasses import dataclass
import requests
import pickle
from enum import Enum

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
from proof_retrieval.proof_idx import ProofIdx
from proof_retrieval.tfidf import tf_idf
from proof_retrieval.bm25 import bm25
from proof_retrieval.mine_goals import FileGoals, GoalRecord
from proof_retrieval.transform_ast import AdjTree
from proof_retrieval.retrieved_proof_db import StepID

from util.util import FlexibleUrl
from util.util import get_basic_logger
from util.constants import PROOF_VECTOR_DB_METADATA

_logger = get_basic_logger(__name__)


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


# @dataclass
# class TreeProofRetrieverConf:
#     proof_bank_loc: Path
#     max_steps: int
#     max_proofs: int
#     data_loc: Path
#     sentence_db_loc: Path
#     ALIAS = "tree"

#     @classmethod
#     def from_yaml(cls, yaml_data: Any) -> TreeProofRetrieverConf:
#         return cls(
#             Path(yaml_data["proof_bank_loc"]),
#             yaml_data["max_steps"],
#             yaml_data["max_proofs"],
#             Path(yaml_data["data_loc"]),
#             Path(yaml_data["sentence_db_loc"]),
#         )


# class TreeProofRetriever:
#     def __init__(
#         self,
#         proof_bank_loc: Path,
#         max_steps: int,
#         max_proofs: int,
#         data_loc: Path,
#         sentence_db: SentenceDB,
#     ):
#         self.proof_bank_loc = proof_bank_loc
#         self.max_steps = max_steps
#         self.max_proofs = max_proofs
#         self.data_loc = data_loc
#         self.sentence_db = sentence_db
#         self.dp_cache = DPCache()

#     @functools.lru_cache()
#     def __get_file_goals(self, key: str) -> Optional[FileGoals]:
#         goal_loc = os.path.join(self.proof_bank_loc, key)
#         if not os.path.exists(goal_loc):
#             return None
#         goals = FileGoals.load(goal_loc)
#         return goals

#     def get_record_and_cutoff_index(
#         self, step_idx: int, proof: Proof, file_goals: FileGoals
#     ) -> Optional[tuple[int, int]]:
#         current_ground_truth = [s.step.text for s in proof.steps[step_idx:]]
#         complete_ground_truth = [s.step.text for s in proof.steps]
#         record_idx: Optional[int] = None
#         cur_ground_truth_str = "".join(current_ground_truth)
#         if len(proof.steps[step_idx].goals) <= 0:
#             return None
#         norm_pretty_proof_goal = " ".join(
#             proof.steps[step_idx].goals[0].to_string().split()
#         )
#         for i, record in enumerate(file_goals.records):
#             record_proof_str = "".join(record.proof)
#             norm_record_goal = " ".join(record.pretty_goal.split())
#             if norm_record_goal == norm_pretty_proof_goal and (
#                 cur_ground_truth_str.startswith(record_proof_str)
#                 or record_proof_str.startswith(cur_ground_truth_str)
#             ):
#                 record_idx = i
#                 break
#         if record_idx is None:
#             return None

#         prefix_len = len(complete_ground_truth) - len(current_ground_truth)
#         current_record = file_goals.records[record_idx]
#         proof_start_idx = current_record.step_idx - prefix_len
#         return record_idx, proof_start_idx

#     def get_in_file_candidates(
#         self, cutoff_idx: int, file_goals: Optional[FileGoals], file_dp_name: str
#     ) -> list[tuple[GoalRecord, str]]:
#         if file_goals is None:
#             return []
#         candidate_records: list[tuple[GoalRecord, str]] = []
#         for record in file_goals.records:
#             if cutoff_idx <= record.step_idx:
#                 break
#             candidate_records.append((record, file_dp_name))
#         return candidate_records

#     def get_out_of_file_candidates(
#         self, dp_obj: DatasetFile
#     ) -> list[tuple[GoalRecord, str]]:
#         candidates: list[tuple[GoalRecord, str]] = []
#         for dependency in dp_obj.dependencies:
#             dependency_goals = self.__get_file_goals(dependency)
#             if dependency_goals is None:
#                 continue
#             for record in dependency_goals.records:
#                 candidates.append((record, dependency))
#         return candidates

#     def get_whole_proof(
#         self, candidate: ProofCandidateReversed, data_loc: Path, sentence_db: SentenceDB
#     ) -> tuple[Proof, str]:
#         candidate_dp = self.dp_cache.get_dp(candidate.origin, data_loc, sentence_db)
#         record_proof_str = " ".join("".join(candidate.candidate.proof).split())
#         pretty_candidate_goal = " ".join(candidate.candidate.pretty_goal.split())
#         for proof in candidate_dp.proofs:
#             for i, step in enumerate(proof.steps):
#                 if 0 == len(step.goals):
#                     continue
#                 current_ground_truth = [s.step.text for s in proof.steps[i:]]
#                 cur_ground_truth_str = " ".join("".join(current_ground_truth).split())
#                 pretty_proof_goal = " ".join(step.goals[0].to_string().split())
#                 if pretty_candidate_goal == pretty_proof_goal and (
#                     cur_ground_truth_str.startswith(record_proof_str)
#                     or record_proof_str.startswith(cur_ground_truth_str)
#                 ):
#                     return proof, candidate.origin
#         print(candidate.candidate.pretty_goal)
#         raise ValueError(
#             "Could not find corresponding candidate's corresponding proof."
#         )

#     def get_similar_proofs(
#         self,
#         step_idx: int,
#         proof: Proof,
#         dp_obj: DatasetFile,
#         file_info: FileInfo,
#         key_record: Optional[GoalRecord] = None,
#         cutoff_idx: Optional[int] = None,
#         max_num_nodes: int = 30,
#         max_num_steps: int = 500,
#     ):
#         candidates = self.get_similar_goal_records(
#             step_idx,
#             proof,
#             dp_obj,
#             file_info,
#             key_record,
#             cutoff_idx,
#             max_num_nodes,
#             max_num_steps,
#         )
#         seen_proofs: set[str] = set()
#         similar_whole_proofs: list[Proof] = []
#         for c in candidates:
#             try:
#                 proof_obj, origin = self.get_whole_proof(
#                     c, self.data_loc, self.sentence_db
#                 )
#                 proof_str = proof_obj.proof_text_to_string()
#                 if proof_str in seen_proofs:
#                     continue
#                 seen_proofs.add(proof_str)
#                 if self.max_proofs <= len(seen_proofs):
#                     break
#                 similar_whole_proofs.append(proof_obj)
#             except ValueError:
#                 _logger.warning(f"Couldn't find corresponding proof with {c.origin}")
#         return similar_whole_proofs

#     def get_similar_goal_records(
#         self,
#         step_idx: int,
#         proof: Proof,
#         dp_obj: DatasetFile,
#         file_info: FileInfo,
#         key_record: Optional[GoalRecord] = None,
#         cutoff_idx: Optional[int] = None,
#         max_num_nodes: int = 30,
#         max_num_steps: int = 500,
#     ) -> list[ProofCandidateReversed]:
#         file_goals = self.__get_file_goals(file_info.dp_name)
#         if key_record is None and cutoff_idx is None:
#             if file_goals is None:
#                 return []
#             record_result = self.get_record_and_cutoff_index(
#                 step_idx, proof, file_goals
#             )
#             if record_result is None:
#                 return []
#             record_idx, cutoff_idx = record_result
#             key_record = file_goals.records[record_idx]
#         elif key_record is None or cutoff_idx is None:
#             return []

#         in_file_candidates = self.get_in_file_candidates(
#             cutoff_idx, file_goals, file_info.dp_name
#         )
#         in_file_candidates.reverse()
#         out_of_file_candidates = self.get_out_of_file_candidates(dp_obj)
#         all_raw_candidates = in_file_candidates + out_of_file_candidates
#         key_prefix = key_record.term.get_breadth_prefix(max_num_nodes)
#         key_adjtree = AdjTree.from_stree(key_prefix)

#         best_record_candiates: list[ProofCandidateReversed] = []
#         if max_num_steps < len(all_raw_candidates):
#             selected_raw_candidates = random.sample(all_raw_candidates, max_num_steps)
#         else:
#             selected_raw_candidates = all_raw_candidates

#         for c, o in selected_raw_candidates:
#             c_prefix = c.term.get_breadth_prefix(max_num_nodes)
#             c_adjtree = AdjTree.from_stree(c_prefix)
#             c_distance = key_adjtree.distance(c_adjtree)
#             heapq.heappush(
#                 best_record_candiates, ProofCandidateReversed(c_distance, c, o)
#             )
#             if self.max_steps < len(best_record_candiates):
#                 heapq.heappop(best_record_candiates)
#         sorted_candidates = heapq.nlargest(
#             len(best_record_candiates), best_record_candiates
#         )
#         return sorted_candidates

#     @classmethod
#     def from_conf(cls, conf: TreeProofRetrieverConf) -> TreeProofRetriever:
#         return cls(
#             conf.proof_bank_loc,
#             conf.max_steps,
#             conf.max_proofs,
#             conf.data_loc,
#             SentenceDB.load(conf.sentence_db_loc),
#         )


class SparseKind(Enum):
    TFIDF = 0
    BM25 = 1

    @classmethod
    def from_str(cls, s: str) -> SparseKind:
        match s:
            case "tfidf":
                return SparseKind.TFIDF
            case "bm25":
                return SparseKind.BM25
            case _:
                raise ValueError(f"Unknown sparse kind: {s}")


@dataclass
class SparseProofRetrieverConf:
    kind: str
    max_examples: int
    data_loc: Path
    sentence_db_loc: Path
    ALIAS = "sparse"

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> SparseProofRetrieverConf:
        return cls(
            yaml_data["kind"],
            yaml_data["max_examples"],
            Path(yaml_data["data_loc"]),
            Path(yaml_data["sentence_db_loc"]),
        )


def get_available_proofs(
    key_proof: Proof,
    dp_obj: DatasetFile,
    dp_cache: DPCache,
    data_loc: Path,
    sentence_db: SentenceDB,
) -> list[tuple[Proof, DatasetFile]]:
    available_proofs: list[tuple[Proof, DatasetFile]] = []
    for proof in dp_obj.proofs:
        if proof == key_proof:
            break
        available_proofs.append((proof, dp_obj))

    # print("Dependencies", dp_obj.dependencies)
    for dep in dp_obj.dependencies:
        try:
            dep_obj = dp_cache.get_dp(dep, data_loc, sentence_db)
        except FileNotFoundError:
            _logger.warning(f"Could not find dependency: {dep}")
            continue
        for proof in dep_obj.proofs:
            available_proofs.append((proof, dep_obj))
    return available_proofs


class SparseProofRetriever:
    def __init__(
        self,
        kind: SparseKind,
        max_examples: int,
        data_loc: Path,
        sentence_db: SentenceDB,
    ) -> None:
        self.max_examples = max_examples
        self.data_loc = data_loc
        self.sentence_db = sentence_db
        self.dp_cache = DPCache()

    def get_goal_ids(self, goals: list[Goal]) -> list[str]:
        ids: list[str] = []
        for g in goals:
            hyp_ids, goal_ids = get_ids_from_goal(g)
            ids.extend(hyp_ids)
            ids.extend(goal_ids)
        return ids

    def get_similar_proof_steps(
        self,
        step_idx: int,
        proof: Proof,
        dp_obj: DatasetFile,
        **kwargs: Any,
    ) -> list[tuple[Proof, StepID]]:
        key_step = proof.steps[step_idx]
        if len(key_step.goals) == 0:
            return []
        query_ids = self.get_goal_ids(key_step.goals)
        available_proofs = get_available_proofs(
            proof, dp_obj, self.dp_cache, self.data_loc, self.sentence_db
        )
        reference_proofs: list[Proof] = []
        reference_dp_files: list[DatasetFile] = []
        reference_step_idxs: list[int] = []
        docs: list[list[str]] = []
        for ref_proof, ref_dp in available_proofs:
            for step_idx, step in enumerate(ref_proof.steps):
                reference_dp_files.append(ref_dp)
                reference_proofs.append(ref_proof)
                reference_step_idxs.append(step_idx)
                docs.append(self.get_goal_ids(step.goals))
        assert len(docs) == len(reference_proofs)
        scores = bm25(query_ids, docs)
        arg_sorted_scores = sorted(range(len(scores)), key=lambda idx: -1 * scores[idx])

        references = list(
            zip(reference_proofs, reference_dp_files, reference_step_idxs)
        )
        similar_proof_steps: list[tuple[Proof, StepID]] = []
        distinct_proofs: set[tuple[str, int]] = set()
        for proof_idx in arg_sorted_scores:
            ref_proof, ref_dp, ref_step_idx = references[proof_idx]
            key = (ref_dp.dp_name, ref_proof.proof_idx)
            distinct_proofs.add(key)
            similar_proof_steps.append(
                (ref_proof, StepID(ref_dp.dp_name, ref_proof.proof_idx, ref_step_idx))
            )
            if self.max_examples <= len(distinct_proofs):
                break
        return similar_proof_steps

    def get_similar_proofs(
        self, key_step_idx: int, key_proof: Proof, dp_obj: DatasetFile, **kwargs: Any
    ) -> list[Proof]:
        similar_proof_steps = self.get_similar_proof_steps(
            key_step_idx, key_proof, dp_obj
        )
        similar_proofs: list[Proof] = []
        distinct_proofs: set[tuple[str, int]] = set()
        for proof, step_id in similar_proof_steps:
            if (step_id.file, step_id.proof_idx) in distinct_proofs:
                continue
            distinct_proofs.add((step_id.file, step_id.proof_idx))
            similar_proofs.append(proof)
        return similar_proofs

    @classmethod
    def from_conf(cls, conf: SparseProofRetrieverConf) -> SparseProofRetriever:
        return cls(
            SparseKind.from_str(conf.kind),
            conf.max_examples,
            conf.data_loc,
            SentenceDB.load(conf.sentence_db_loc),
        )


@dataclass
class DeepProofRetrieverConf:
    ALIAS = "deep"
    model_name: str | Path
    vector_db_loc: Path
    max_seq_len: int
    max_num_proofs: int
    sentence_db_loc: Path
    data_loc: Path

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> DeepProofRetrieverConf:
        model_name = yaml_data["model_name"]
        if os.path.exists(model_name):
            model_name = Path(model_name)
        vector_db_loc = Path(yaml_data["vector_db_loc"])
        sentence_db_loc = Path(yaml_data["sentence_db_loc"])
        data_loc = Path(yaml_data["data_loc"])
        return cls(
            model_name,
            vector_db_loc,
            yaml_data["max_seq_len"],
            yaml_data["max_num_proofs"],
            sentence_db_loc,
            data_loc,
        )


@dataclass
class DeepProofRetrieverClientConf:
    urls: list[FlexibleUrl]
    vector_db_loc: Path
    sentence_db_loc: Path
    data_loc: Path
    max_num_proofs: int
    ALIAS = "deep-client"

    def merge(
        self, other: DeepProofRetrieverClientConf
    ) -> DeepProofRetrieverClientConf:
        return DeepProofRetrieverClientConf(
            self.urls + other.urls,
            self.vector_db_loc,
            self.sentence_db_loc,
            self.data_loc,
            self.max_num_proofs,
        )

    def update_ips(self, port_map: dict[int, tuple[str, int]]):
        for url in self.urls:
            new_ip, new_port = port_map[url.id]
            url.ip = new_ip
            url.port = new_port

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> DeepProofRetrieverClientConf:
        raise NotImplementedError()


@dataclass
class ProofDBQuery:
    step_idx: int
    proof: Proof
    dp_name: str

    def format(self) -> str:
        goal_sep = "\n[GOAL]\n"
        goal_strings = [g.to_string() for g in self.proof.steps[self.step_idx].goals]
        return goal_sep.join(goal_strings)


# will need to do proofs + premises but this is good for now
class DeepProofRetrieverClient:
    def __init__(
        self,
        urls: list[str],
        proof_idx: ProofIdx,
        sentence_db: SentenceDB,
        data_loc: Path,
        max_num_proofs: int,
    ):
        self.urls = urls
        self.proof_idx = proof_idx
        self.data_loc = data_loc
        self.sentence_db = sentence_db
        self.max_num_proofs = max_num_proofs
        self.dp_cache = DPCache()
        self.session = requests.Session()

    def get_available_proofs(
        self, key_proof: Proof, dp_obj: DatasetFile
    ) -> list[tuple[Proof, DatasetFile]]:
        return get_available_proofs(
            key_proof, dp_obj, self.dp_cache, self.data_loc, self.sentence_db
        )

    def get_similar_proof_steps(
        self,
        step_idx: int,
        proof: Proof,
        dp_obj: DatasetFile,
        **kwargs: Any,
    ) -> list[tuple[Proof, StepID]]:
        hashed_step_idx = self.proof_idx.hash_proof_step(
            step_idx, proof, dp_obj.dp_name
        )
        if self.proof_idx.contains(hashed_step_idx):
            query_step_idx = self.proof_idx.get_idx(hashed_step_idx)
        else:
            query_step_idx = None
        # HARD CODED
        goal_str = ProofDBQuery(step_idx, proof, dp_obj.dp_name).format()
        available_proofs_and_objs = self.get_available_proofs(proof, dp_obj)
        available_proof_idxs: list[int] = []
        available_proof_steps: list[tuple[Proof, StepID]] = []
        for p, dep_obj in available_proofs_and_objs:
            for i, step in enumerate(p.steps):
                try:
                    step_hash = self.proof_idx.hash_proof_step(i, p, dep_obj.dp_name)
                    step_idx = self.proof_idx.get_idx(step_hash)
                    available_proof_idxs.append(step_idx)
                    available_proof_steps.append((p, StepID(dep_obj.dp_name, p.proof_idx, i)))
                except KeyError:
                    _logger.error(f"Could not find step {i} in {dep_obj.dp_name}")
                    return []

        request_url = random.choice(self.urls)
        request_data = {
            "method": "get_scores",
            "params": [goal_str, available_proof_idxs, query_step_idx],
            "jsonrpc": "2.0",
            "id": 0,
        }
        response = self.session.post(request_url, json=request_data).json()
        scores = response["result"]
        assert len(available_proof_steps) == len(scores)
        similar_proof_steps = sorted(
            range(len(available_proof_steps)), key=lambda idx: -1 * scores[idx]
        )
        similar_steps: list[tuple[Proof, StepID]] = []
        for i in similar_proof_steps:
            similar_steps.append(available_proof_steps[i])
        return similar_steps

    def get_similar_proofs(
        self,
        key_step_idx: int,
        key_proof: Proof,
        dp_obj: DatasetFile,
        **kwargs: Any,
    ) -> list[Proof]:
        similar_proof_steps = self.get_similar_proof_steps(
            key_step_idx, key_proof, dp_obj
        )
        similar_proofs: list[Proof] = []
        seen_proofs: set[str] = set()
        for p, i in similar_proof_steps:
            proof_key = p.proof_text_to_string()
            if proof_key in seen_proofs:
                continue
            seen_proofs.add(proof_key)
            similar_proofs.append(p)
            if self.max_num_proofs <= len(similar_proofs):
                break
        return similar_proofs

    @classmethod
    def from_conf(cls, conf: DeepProofRetrieverClientConf) -> DeepProofRetrieverClient:
        metadata_loc = conf.vector_db_loc / PROOF_VECTOR_DB_METADATA
        with metadata_loc.open("rb") as fin:
            metadata = pickle.load(fin)
        proof_idx = metadata["proof_idx"]
        sentence_db = SentenceDB.load(conf.sentence_db_loc)
        return cls(
            [u.get_url() for u in conf.urls],
            proof_idx,
            sentence_db,
            conf.data_loc,
            conf.max_num_proofs,
        )


ProofRetrieverConf = (
    SparseProofRetrieverConf | DeepProofRetrieverClientConf | DeepProofRetrieverConf
)

ProofRetriever = SparseProofRetriever | DeepProofRetrieverClient


def proof_conf_update_ips(c: ProofRetrieverConf, port_map: dict[int, tuple[str, int]]):
    match c:
        case DeepProofRetrieverClientConf():
            c.update_ips(port_map)
        case _:
            pass


def merge_proof_confs(
    c1: ProofRetrieverConf, c2: ProofRetrieverConf
) -> ProofRetrieverConf:
    match c1:
        case DeepProofRetrieverClientConf():
            assert isinstance(c2, DeepProofRetrieverClientConf)
            return c1.merge(c2)
        case _:
            assert c1 == c2
            return c1


def close_proof_retriever(retriever: ProofRetriever):
    match retriever:
        case SparseProofRetriever() | DeepProofRetrieverClient():
            retriever.sentence_db.close()


def proof_retriever_from_conf(conf: ProofRetrieverConf) -> ProofRetriever:
    match conf:
        case SparseProofRetrieverConf():
            return SparseProofRetriever.from_conf(conf)
        case DeepProofRetrieverClientConf():
            return DeepProofRetrieverClient.from_conf(conf)
        case DeepProofRetrieverConf():
            raise ValueError("Cannot directly instantiate deep proof retriever.")


def proof_retriever_conf_from_yaml(yaml_data: Any) -> ProofRetrieverConf:
    attempted_alias = yaml_data["alias"]
    match attempted_alias:
        case SparseProofRetrieverConf.ALIAS:
            return SparseProofRetrieverConf.from_yaml(yaml_data)
        case DeepProofRetrieverClientConf.ALIAS:
            return DeepProofRetrieverClientConf.from_yaml(yaml_data)
        case DeepProofRetrieverConf.ALIAS:
            return DeepProofRetrieverConf.from_yaml(yaml_data)
        case _:
            raise ValueError(f"Proof retriever alias: {attempted_alias} not found.")
