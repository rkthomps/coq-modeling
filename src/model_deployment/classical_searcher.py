from __future__ import annotations
import heapq
import time
from typing import Optional, Any
from dataclasses import dataclass
from data_management.dataset_file import Proof, DatasetFile
from model_deployment.proof_manager import ProofManager, TacticResult
from model_deployment.tactic_gen_client import TacticGenClient
from model_deployment.goal_comparer import AlphaGoalComparer

from coqpyt.coq.lsp.structs import Goal


@dataclass
class ClassicalSearchConf:
    max_branch: int
    max_search_steps: int
    depth_limit: int
    timeout: int
    beam_decode: bool
    initial_proof: Optional[str]
    ALIAS = "classical"

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> ClassicalSearchConf:
        return cls(
            yaml_data["max_branch"],
            yaml_data["max_search_steps"],
            yaml_data["depth_limit"],
            yaml_data["timeout"],
            yaml_data["beam_decode"],
            yaml_data.get("initial_proof", None),
        )


@dataclass
class ClassicalSuccess:
    time: float
    model_time: float
    search_steps: int
    successful_candidate: Candidate
    root_candidate: Candidate


@dataclass
class ClassicalFailure:
    time: float
    model_time: float
    search_steps: int
    root_candidate: Candidate


class Candidate:
    def __init__(
        self,
        proof: Optional[Proof],
        proof_str: str,
        tactic: str,
        score: float,
        tactic_score: float,
        depth: int,
        children: Optional[list[Candidate]],
    ):
        self.proof = proof
        self.proof_str = proof_str
        self.tactic = tactic
        self.score = score
        self.tactic_score = tactic_score
        self.depth = depth
        if children is None:
            self.children = []
        else:
            self.children = children

    def __lt__(self, other: Candidate) -> bool:
        return other.score <= self.score  # Reversed so higher scores are first in pq


class ClassicalSearcher:
    def __init__(
        self,
        tactic_client: TacticGenClient,
        proof_manager: ProofManager,
        max_branch: int,
        max_search_steps: int,
        depth_limit: int,
        timeout: int,
        beam_decode: bool,
        initial_proof: Optional[str] = None,
    ):
        self.tactic_client = tactic_client
        self.proof_manager = proof_manager
        self.max_branch = max_branch
        self.max_search_steps = max_search_steps
        self.depth_limit = depth_limit
        self.timeout = timeout
        self.beam_decode = beam_decode
        self.initial_proof = initial_proof

        initial_dset_file = proof_manager.get_initial_context()
        if initial_dset_file is None:
            raise ValueError("Could not get initial datasetfile")
        self.initial_dset_file = initial_dset_file

        if initial_proof is None:
            initial_proof = ""

        self.need_goal_record = False
        self.total_model_time = 0

        self.comparer = AlphaGoalComparer()

        self.root_candidate = Candidate(None, "", initial_proof, 0, 0, 0, None)
        self.frontier: list[Candidate] = []
        self.seen_goals: list[list[Goal]] = []
        self.seen_goals_candidates: list[Candidate] = []
        heapq.heappush(self.frontier, self.root_candidate)

    @classmethod
    def from_conf(
        cls,
        conf: ClassicalSearchConf,
        tactic_clients: list[TacticGenClient],
        proof_manager: ProofManager,
    ) -> ClassicalSearcher:
        assert len(tactic_clients) == 1
        return cls(
            tactic_clients[0],
            proof_manager,
            conf.max_branch,
            conf.max_search_steps,
            conf.depth_limit,
            conf.timeout,
            conf.beam_decode,
            conf.initial_proof,
        )

    def search(
        self, print_proofs: bool = False, print_trees: bool = False
    ) -> ClassicalSuccess | ClassicalFailure:
        start = time.time()
        num_steps = 0
        for i in range(self.max_search_steps):
            cur = time.time()
            if self.timeout <= cur - start:
                return ClassicalFailure(
                    cur - start, self.total_model_time, num_steps, self.root_candidate
                )
            if len(self.frontier) == 0:
                return ClassicalFailure(
                    cur - start, self.total_model_time, num_steps, self.root_candidate
                )
            num_steps += 1
            possible_success = self.search_step(num_steps, print_proofs)
            if possible_success is not None:
                return ClassicalSuccess(
                    time.time() - start,
                    self.total_model_time,
                    num_steps,
                    possible_success,
                    self.root_candidate,
                )
        return ClassicalFailure(
            time.time() - start, self.total_model_time, num_steps, self.root_candidate
        )

    # Delay checking until node is selected
    def is_only_focusing(self, tactic: str) -> bool:
        stripped_tactic = tactic.strip()
        return all([c in "*-+" for c in stripped_tactic])

    def is_only_proof(self, tactic: str) -> bool:
        # could ensure that the tactic is the first proof tactic
        return tactic.strip() == "Proof."

    def is_redundant(self, candidate: Candidate, candidate_goals: list[Goal]) -> bool:
        if self.is_only_focusing(candidate.tactic) or self.is_only_proof(
            candidate.tactic
        ):
            return False
        for seen_goals in self.seen_goals:
            if self.comparer.as_hard_as(
                candidate_goals,
                seen_goals,
                self.proof_manager.fast_client,
                self.proof_manager.file_prefix,
            ):
                return True
        return False

    def search_step(self, attempt_num: int, print_proofs: bool) -> Optional[Candidate]:
        cur_candidate = heapq.heappop(self.frontier)
        if print_proofs:
            print(f"===== Attempt {attempt_num} ======")
            print(cur_candidate.proof_str)
            print()
        proof_check_result = self.proof_manager.check_proof(
            cur_candidate.proof_str,
            self.initial_dset_file.proofs[-1].theorem,
        )
        match proof_check_result.tactic_result:
            case TacticResult.COMPLETE:
                assert proof_check_result.new_proof is not None
                cur_candidate.proof = proof_check_result.new_proof
                return cur_candidate
            case TacticResult.INVALID:
                return None
            case TacticResult.VALID:
                assert proof_check_result.new_proof is not None
                assert proof_check_result.current_goals is not None
                cur_candidate.proof = proof_check_result.new_proof
                cur_dset_file = self.proof_manager.build_dset_file(cur_candidate.proof)
                if self.is_redundant(cur_candidate, proof_check_result.current_goals):
                    return None
                if self.depth_limit <= cur_candidate.depth:
                    return None
                self.seen_goals.append(proof_check_result.current_goals)
                self.seen_goals_candidates.append(cur_candidate)
                start_time = time.time()
                recs = self.tactic_client.get_recs(
                    len(cur_candidate.proof.steps) - 1,
                    cur_candidate.proof,
                    cur_dset_file,
                    self.max_branch,
                    beam=self.beam_decode,
                    file_prefix=self.proof_manager.file_prefix,
                )
                end_time = time.time()
                self.total_model_time += end_time - start_time
                for tactic, tactic_score, num_tokens in zip(
                    recs.next_tactic_list, recs.score_list, recs.num_tokens_list
                ):
                    admitted_step = cur_candidate.proof.steps[-1]
                    proof_str = (
                        cur_candidate.proof.proof_prefix_to_string(
                            admitted_step, include_theorem=False
                        )
                        + tactic
                    )
                    score = cur_candidate.score + tactic_score
                    depth = cur_candidate.depth + 1
                    new_candidate = Candidate(
                        None, proof_str, tactic, score, tactic_score, depth, None
                    )
                    cur_candidate.children.append(new_candidate)
                    heapq.heappush(self.frontier, new_candidate)
