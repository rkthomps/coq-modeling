from __future__ import annotations
from typing import Optional, Any
import heapq
import time
import ipdb
import re
from dataclasses import dataclass

import sys, os

from coqpyt.coq.lsp.structs import Goal
from util.coqpyt_utils import get_all_goals

from model_deployment.model_result import ModelResult, filter_recs
from model_deployment.tactic_gen_client import TacticGenClient
from model_deployment.node_score import NodeScore, OverrideScore, NODE_SCORE_ALIASES
from model_deployment.proof_manager import ProofManager, TacticResult, ProofCheckResult
from model_deployment.search_tree import SearchNode, SearchTree
from model_deployment.goal_comparer import AlphaGoalComparer, GoalScorer
from util.util import get_basic_logger

from data_management.sentence_db import SentenceDB
from data_management.dataset_file import DatasetFile, Proof
from tactic_gen.lm_example import (
    LmExample,
)


_logger = get_basic_logger(__name__)


class ClassicalSuccess:
    def __init__(
        self,
        search_tree: SearchTree,
        qed_node: SearchNode,
        total_model_time: float,
        total_search_time: float,
    ) -> None:
        self.search_tree = search_tree
        self.qed_node = qed_node
        self.total_model_time = total_model_time
        self.total_search_time = total_search_time

    def get_proof(self) -> str:
        return self.qed_node.steps_to_str(self.qed_node.combined_proof_steps)


class ClassicalFailure:
    def __init__(
        self, search_tree: SearchTree, total_model_time: float, total_search_time: float
    ) -> None:
        self.search_tree = search_tree
        self.total_model_time = total_model_time
        self.total_search_time = total_search_time


class ErroredSearch:
    ALIAS = "error"

    def __init__(self, message: str, error_after: float) -> None:
        self.message = message
        self.error_after = error_after

    def to_json(self, sentence_db: SentenceDB) -> Any:
        return {
            "message": self.message,
            "error_after": self.error_after,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> Any:
        return cls(json_data["message"], json_data["error_after"])


@dataclass
class ClassicalSearchConf:
    ALIAS = "classical"
    node_score_alias: str
    max_branch: int
    max_expansions: int
    depth_limit: int
    timeout: int
    beam_decode: bool
    initial_proof: Optional[str]

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> ClassicalSearchConf:
        if "initial_proof" not in yaml_data:
            initial_proof = None
        else:
            initial_proof = yaml_data["initial_proof"]
        return cls(
            yaml_data["node_score_alias"],
            yaml_data["max_branch"],
            yaml_data["max_expansions"],
            yaml_data["depth_limit"],
            yaml_data["timeout"],
            yaml_data["beam_decode"],
            initial_proof,
        )


class ClassicalSearcher:
    def __init__(
        self,
        tactic_client: TacticGenClient,
        proof_manager: ProofManager,
        score_type: type[NodeScore],
        max_branch: int,
        max_num_leaf_expansions: int,
        depth_limit: int,
        timeout: int,
        beam_decode: bool,
        initial_proof: Optional[str] = None,
    ) -> None:
        self.tactic_client = tactic_client
        self.proof_manager = proof_manager
        self.score_type = score_type
        self.max_branch = max_branch
        self.max_num_leaf_expansions = max_num_leaf_expansions
        self.depth_limit = depth_limit
        self.timeout = timeout
        self.beam_decode = beam_decode

        self.stop_early = initial_proof is not None
        if initial_proof is None:
            initial_proof = ""

        # print("INITIAL PROOF:")
        # print(initial_proof)

        initial_validity = True
        final_tactic = False
        makes_progress = True
        self.comparer = AlphaGoalComparer()
        self.total_model_time = 0

        initial_dset_file = proof_manager.get_initial_context()
        if initial_dset_file is None:
            raise ValueError("Could not get initial datasetfile")
        self.goal_scorer = self.__get_goal_scorer(initial_dset_file)
        self.initial_proof_obj = initial_dset_file.proofs[-1]
        initial_check_result = proof_manager.check_proof(
            initial_proof, self.initial_proof_obj.theorem, self.need_goal_record
        )
        # print(initial_check_result)
        assert initial_check_result.tactic_result == TacticResult.VALID
        assert initial_check_result.current_goals is not None
        assert initial_check_result.new_proof is not None

        self.initial_num_goals = len(initial_check_result.current_goals)

        combined_valid_steps: list[str] = initial_check_result.attempted_steps
        initial_proof = SearchNode.steps_to_str(combined_valid_steps)
        initial_score = self.score_type.get_initial_score(max_branch)
        creation_time = -1
        self.root = SearchNode(
            initial_validity,
            final_tactic,
            makes_progress,
            initial_proof,
            combined_valid_steps,
            initial_score,
            creation_time,
            initial_check_result.new_proof,
            initial_check_result.goal_record,
            depth=0,
        )
        self.search_tree = SearchTree(initial_dset_file.file_context, self.root)
        self.frontier: list[tuple[SearchNode, list[Goal]]] = []
        self.seen_goals: list[list[Goal]] = []
        self.seen_goals_nodes: list[SearchNode] = []
        heapq.heappush(self.frontier, (self.root, initial_check_result.current_goals))

    @classmethod
    def from_conf(
        cls,
        conf: ClassicalSearchConf,
        tactic_gen_client: TacticGenClient,
        manager: ProofManager,
    ) -> ClassicalSearcher:
        return cls(
            tactic_gen_client,
            manager,
            NODE_SCORE_ALIASES[conf.node_score_alias],
            conf.max_branch,
            conf.max_expansions,
            conf.depth_limit,
            conf.timeout,
            conf.beam_decode,
            conf.initial_proof,
        )

    @property
    def need_goal_record(self):
        return False

    def search(
        self, print_trees: bool = False, print_proofs: bool = False
    ) -> ClassicalSuccess | ClassicalFailure:
        start = time.time_ns()
        for i in range(self.max_num_leaf_expansions):
            cur = time.time_ns()
            if ((cur - start) / 1e9) > self.timeout:
                _logger.debug(f"failure by timeout of {self.timeout}")
                break
            if len(self.frontier) == 0:
                break
            self.proof_manager.fast_client.client.lsp_endpoint.timeout = 5
            possible_complete_node = self.search_step(i + 1, start, print_proofs)
            if print_trees:
                self.search_tree.pretty_print(verbose=True)
            if possible_complete_node:
                cur = time.time_ns()
                return ClassicalSuccess(
                    self.search_tree,
                    possible_complete_node,
                    self.total_model_time,
                    cur - start,
                )
        cur = time.time_ns()
        return ClassicalFailure(self.search_tree, self.total_model_time, cur - start)

    def __get_goal_scorer(self, dset_file: DatasetFile) -> GoalScorer:
        avail_lemmmas: list[str] = []
        for p in dset_file.in_file_avail_premises:
            if p.is_lemma_or_axiom():
                avail_lemmmas.append(p.text)
        for p in dset_file.out_of_file_avail_premises:
            if p.is_lemma_or_axiom():
                avail_lemmmas.append(p.text)
        return GoalScorer(avail_lemmmas)

    def __get_complete_child_node(
        self,
        proof_check_result: ProofCheckResult,
        attempted_tactic: str,
        parent_node: SearchNode,
        score: NodeScore,
        search_start_time: int,
    ) -> SearchNode:
        assert proof_check_result.current_goals is not None
        assert proof_check_result.current_goals == [] or (
            self.stop_early
            and len(proof_check_result.current_goals) < self.initial_num_goals
        )
        valid = True
        final_tactic = True
        makes_progress = True
        creation_time = time.time_ns() - search_start_time
        assert parent_node.depth is not None
        complete_node = SearchNode(
            valid,
            final_tactic,
            makes_progress,
            attempted_tactic,
            proof_check_result.attempted_steps,
            parent_node.score.agg(score),
            creation_time,
            proof_check_result.new_proof,
            proof_check_result.goal_record,
            depth=parent_node.depth + 1,
        )
        return complete_node

    def __get_invalid_child_node(
        self,
        proof_check_result: ProofCheckResult,
        attempted_tactic: str,
        parent_node: SearchNode,
        score: NodeScore,
        search_start_time: int,
    ) -> SearchNode:
        assert proof_check_result.current_goals is None
        valid = False
        final_tactic = False
        makes_progress = False
        combined_steps = proof_check_result.attempted_steps
        creation_time = time.time_ns() - search_start_time
        assert parent_node.depth is not None
        invalid_node = SearchNode(
            valid,
            final_tactic,
            makes_progress,
            attempted_tactic,
            combined_steps,
            parent_node.score.agg(score),
            creation_time,
            proof_check_result.new_proof,
            proof_check_result.goal_record,
            depth=parent_node.depth + 1,
        )
        return invalid_node

    def as_hard_as(self, gs1: list[Goal], gs2: list[Goal]) -> bool:
        return self.comparer.as_hard_as(
            gs1, gs2, self.proof_manager.goal_client, self.proof_manager.file_prefix
        )

    def __get_valid_child_node(
        self,
        proof_check_result: ProofCheckResult,
        attempted_tactic: str,
        parent_node: SearchNode,
        score: NodeScore,
        search_start_time: int,
    ) -> SearchNode:
        assert proof_check_result.current_goals is not None
        redundant_to = None
        for seen_goals, seen_goal_node in zip(self.seen_goals, self.seen_goals_nodes):
            if self.as_hard_as(proof_check_result.current_goals, seen_goals):
                redundant_to = seen_goal_node
                break

        redundant_to_str = (
            redundant_to.redundant_str() if redundant_to is not None else None
        )
        creation_time = time.time_ns() - search_start_time
        makes_progress = (
            redundant_to is None
            or self.is_only_focusing(attempted_tactic)
            # or self.__is_bullet(attempted_tactic)
            # or self.__is_first_proof_tactic(
            #     parent_node.total_proof_str(), attempted_tactic
            # )
        )
        valid = True
        final_tactic = False
        assert parent_node.depth is not None
        new_leaf = SearchNode(
            valid,
            final_tactic,
            makes_progress,
            attempted_tactic,
            proof_check_result.attempted_steps,
            parent_node.score.agg(score),
            creation_time,
            proof_check_result.new_proof,
            proof_check_result.goal_record,
            redundant_to_str=redundant_to_str,
            depth=parent_node.depth + 1,
        )
        return new_leaf

    def is_only_focusing(self, tactic: str) -> bool:
        stripped_tactic = tactic.strip()
        return all([c in "*-+" for c in stripped_tactic])

    def search_step(
        self,
        step_num: int,
        search_start_time: int,
        print_proofs: bool,
    ) -> Optional[SearchNode]:
        """If the search is completed, return the resulting node in
        the proof search tree."""
        leaf_subtree, _ = heapq.heappop(self.frontier)
        current_proof = "".join(leaf_subtree.combined_proof_steps)
        leaf_subtree.set_expanded_num(step_num)
        assert leaf_subtree.proof is not None
        dset_file = DatasetFile(self.search_tree.file_context, [leaf_subtree.proof])
        # print("nedd goal record:", self.need_goal_record)
        # print("goal record:", leaf_subtree.goal_record)
        examples = [
            self.proof_manager.get_example(f, dset_file, leaf_subtree.goal_record)
            for f in self.tactic_client.formatters
        ]
        if print_proofs:
            print(leaf_subtree.score.compute())
            # print(current_proof)
            print("proof object:")
            print(leaf_subtree.proof.proof_text_to_string(include_theorem=False))
        start_time = time.time()
        recs = self.tactic_client.get_recs()
        result = self.get_all_recs(examples, current_proof)
        end_time = time.time()
        self.total_model_time += end_time - start_time
        next_frontier_pool: list[SearchNode] = []
        next_frontier_goals: list[list[Goal]] = []
        # print(result.next_tactic_list)
        num_invalid = 0
        if (
            len(result.next_tactic_list) == 0
            or len(result.score_list) == 0
            or len(result.num_tokens_list) == 0
        ):
            _logger.error(
                f"ZERO LEN IN TAC; SCORE; NUM TOK: {len(result.next_tactic_list)}; {len(result.score_list)}; {len(result.num_tokens_list)}"
            )
        for tactic, score, num_tokens in zip(
            result.next_tactic_list, result.score_list, result.num_tokens_list
        ):
            cur_time = time.time_ns()
            if self.timeout <= (cur_time - search_start_time) / 1e9:
                return None
            proof_script = leaf_subtree.total_proof_str() + tactic
            proof_check_result = self.proof_manager.check_proof(
                proof_script, leaf_subtree.proof.theorem, self.need_goal_record
            )
            match proof_check_result.tactic_result:
                case TacticResult.COMPLETE:
                    goal_score = 0
                    node_score = self.score_type.from_unit_score(
                        score, num_tokens, goal_score, self.max_branch
                    )
                    complete_node = self.__get_complete_child_node(
                        proof_check_result,
                        tactic,
                        leaf_subtree,
                        node_score,
                        search_start_time,
                    )
                    leaf_subtree.children.append(complete_node)
                    return complete_node

                case TacticResult.INVALID:
                    goal_score = -10000
                    node_score = self.score_type.from_unit_score(
                        score, num_tokens, goal_score, self.max_branch
                    )
                    invalid_node = self.__get_invalid_child_node(
                        proof_check_result,
                        tactic,
                        leaf_subtree,
                        node_score,
                        search_start_time,
                    )
                    num_invalid += 1
                    leaf_subtree.children.append(invalid_node)

                case TacticResult.VALID:
                    assert proof_check_result.current_goals is not None
                    # goal_score = self.goal_scorer.score_goals(
                    #     proof_check_result.current_goals
                    # )
                    goal_score = 1
                    node_score = self.score_type.from_unit_score(
                        score, num_tokens, goal_score, self.max_branch
                    )
                    if (
                        self.stop_early
                        and len(proof_check_result.current_goals)
                        < self.initial_num_goals
                    ):
                        complete_node = self.__get_complete_child_node(
                            proof_check_result,
                            tactic,
                            leaf_subtree,
                            node_score,
                            search_start_time,
                        )
                        leaf_subtree.children.append(complete_node)
                        return complete_node

                    valid_node = self.__get_valid_child_node(
                        proof_check_result,
                        tactic,
                        leaf_subtree,
                        node_score,
                        search_start_time,
                    )

                    leaf_subtree.children.append(valid_node)
                    # We will check again if the candide makes progress to make
                    # sure it isn't superceded by later candidates.
                    if (
                        valid_node.makes_progress
                        and valid_node.depth is not None
                        and valid_node.depth <= self.depth_limit
                    ):
                        assert proof_check_result.current_goals is not None
                        next_frontier_pool.append(valid_node)
                        next_frontier_goals.append(proof_check_result.current_goals)

        for next_canidate, next_goals in zip(next_frontier_pool, next_frontier_goals):
            next_frontier: list[tuple[SearchNode, list[Goal]]] = []
            heapq.heappush(next_frontier, (next_canidate, next_goals))
            self.seen_goals.append(next_goals)
            self.seen_goals_nodes.append(next_canidate)
            for node, goals in self.frontier:
                if not self.as_hard_as(goals, next_goals):
                    heapq.heappush(next_frontier, (node, goals))
                else:
                    node.redundant_to_str = next_canidate.redundant_str()
                    node.makes_progress = False
            self.frontier = next_frontier

        return None
