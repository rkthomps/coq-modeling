from __future__ import annotations
from typing import Optional, Any
from enum import Enum
import heapq
import pdb
import time
import re
import pickle

import sys, os


from tactic_gen.lm_example import LmExample
from model_deployment.model_wrapper import ModelWrapper, ModelResult
from model_deployment.node_score import NodeScore
from model_deployment.goal_comparer import NodeGoal, ParsedObligations
from model_deployment.proof_manager import ProofManager, TacticResult, ProofCheckResult
from model_deployment.search_tree import ProofSearchTree

from coqlspclient.coq_file import CoqFile, GoalAnswer
from coqlspclient.coq_lsp_structs import Goal


class SearchResult:
    def __init__(
        self, search_tree: ProofSearchTree, qed_node: Optional[ProofSearchTree]
    ) -> None:
        self.search_tree = search_tree
        self.qed_node = qed_node

    def found_proof(self) -> bool:
        return self.qed_node is not None

    def get_proof(self) -> str:
        if not self.found_proof():
            raise ValueError("Search did not yeild proof.")
        assert self.qed_node is not None
        return self.qed_node.steps_to_str(self.qed_node.combined_proof_steps)

    def to_json(self) -> Any:
        json_data = {"search_tree": self.search_tree.to_json()}
        if self.qed_node:
            json_data["qed_node"] = self.qed_node.to_json()
        return json_data

    @classmethod
    def eval_from_json(cls, json_data: Any) -> SearchResult:
        """Less precise version of to_json. Good for compatibility."""
        search_tree_data = json_data["search_tree"]
        search_tree = ProofSearchTree.eval_from_json(search_tree_data)
        if "qed_node" in json_data:
            qed_node_data = json_data["qed_node"]
            qed_node = ProofSearchTree.eval_from_json(qed_node_data)
        else:
            qed_node = None
        return cls(search_tree, qed_node)

    @classmethod
    def from_json(cls, json_data: Any) -> SearchResult:
        search_tree_data = json_data["search_tree"]
        search_tree = ProofSearchTree.from_json(search_tree_data)
        if "qed_node" in json_data:
            qed_node_data = json_data["qed_node"]
            qed_node = ProofSearchTree.from_json(qed_node_data)
        else:
            qed_node = None
        return cls(search_tree, qed_node)


class SearchTreeManager:
    def __init__(
        self,
        model_wrapper: ModelWrapper,
        proof_manager: ProofManager,
        score_type: type[NodeScore],
        max_branch: int,
        max_num_leaf_expansions: int,
        timeout: int,
    ) -> None:
        assert isinstance(model_wrapper, ModelWrapper)
        assert type(proof_manager) == ProofManager
        assert type(score_type) == type
        assert type(max_branch) == int
        assert type(max_num_leaf_expansions) == int
        assert type(timeout) == int
        self.model_wrapper = model_wrapper
        self.proof_manager = proof_manager
        self.score_type = score_type
        self.max_branch = max_branch
        self.max_num_leaf_expansions = max_num_leaf_expansions
        self.timeout = timeout
        initial_validity = True
        final_tactic = False
        makes_progress = True
        initial_valid_steps: list[str] = []
        combined_valid_steps: list[str] = []
        initial_tactic = ""
        initial_combined_tactics = ""
        initial_goal = ""
        initial_proof = ProofSearchTree.steps_to_str(combined_valid_steps)
        initial_check_result = proof_manager.check_proof(initial_proof, [])
        assert initial_check_result.tactic_result == TacticResult.VALID
        assert initial_check_result.current_goals is not None
        initial_score = self.score_type.get_initial_score(max_branch)
        creation_time = -1
        self.search_tree = ProofSearchTree(
            initial_validity,
            final_tactic,
            makes_progress,
            initial_valid_steps,
            combined_valid_steps,
            initial_tactic,
            initial_combined_tactics,
            initial_goal,
            initial_score,
            creation_time,
        )
        self.frontier: list[ProofSearchTree] = []
        self.seen_goals: list[ParsedObligations] = []
        self.seen_goals_nodes: list[ProofSearchTree] = []
        heapq.heappush(self.frontier, self.search_tree)

    def __get_request_contents(
        self, combined_proof_steps: list[str], target_combined_steps: str
    ) -> LmExample:
        return self.proof_manager.get_example(
            combined_proof_steps, target_combined_steps
        )

    def search(self) -> SearchResult:
        start = time.time_ns()
        for i in range(self.max_num_leaf_expansions):
            cur = time.time_ns()
            if ((cur - start) / 1e9) > self.timeout:
                break
            if len(self.frontier) == 0:
                break
            print(f"Beginning iteration {i + 1} of search.")
            possible_complete_node = self.search_step(i, start)
            self.search_tree.pretty_print()
            if possible_complete_node is not None:
                return SearchResult(self.search_tree, possible_complete_node)
        return SearchResult(self.search_tree, None)

    def __get_complete_child_node(
        self,
        proof_check_result: ProofCheckResult,
        attempted_tactic: str,
        parent_node: ProofSearchTree,
        score: NodeScore,
        search_start_time: int,
    ) -> ProofSearchTree:
        assert proof_check_result.current_goals is not None
        assert proof_check_result.current_goals.goals is not None
        assert proof_check_result.current_goals.goals.goals == []
        pretty_goal = "complete"
        valid = True
        final_tactic = True
        makes_progress = True
        valid_steps = proof_check_result.valid_steps
        creation_time = time.time_ns() - search_start_time
        combined_tactics = ProofSearchTree.combine_tactics(
            parent_node.combined_model_tactics, attempted_tactic
        )
        combined_steps = parent_node.combined_proof_steps + valid_steps
        complete_node = ProofSearchTree(
            valid,
            final_tactic,
            makes_progress,
            valid_steps,
            combined_steps,
            attempted_tactic,
            combined_tactics,
            pretty_goal,
            parent_node.score.agg(score),
            creation_time,
        )
        return complete_node

    def __get_invalid_child_node(
        self,
        proof_check_result: ProofCheckResult,
        attempted_tactic: str,
        parent_node: ProofSearchTree,
        score: NodeScore,
        search_start_time: int,
    ) -> ProofSearchTree:
        assert proof_check_result.current_goals is None
        valid = False
        final_tactic = False
        makes_progress = False
        pretty_goal = "error"
        combined_tactics = ProofSearchTree.combine_tactics(
            parent_node.combined_model_tactics, attempted_tactic
        )
        invalid_steps = [attempted_tactic]
        combined_steps = parent_node.combined_proof_steps + invalid_steps
        creation_time = time.time_ns() - search_start_time
        invalid_node = ProofSearchTree(
            valid,
            final_tactic,
            makes_progress,
            invalid_steps,
            combined_steps,
            attempted_tactic,
            combined_tactics,
            pretty_goal,
            parent_node.score.agg(score),
            creation_time,
        )
        return invalid_node

    def __get_valid_child_node(
        self,
        proof_check_result: ProofCheckResult,
        attempted_tactic: str,
        parent_node: ProofSearchTree,
        score: NodeScore,
        search_start_time: int,
    ) -> ProofSearchTree:
        assert proof_check_result.current_goals is not None
        assert proof_check_result.current_goals.goals is not None
        assert proof_check_result.parsed_current_goals is not None
        pretty_goal = repr(proof_check_result.current_goals.goals.goals)
        redundant_to = proof_check_result.parsed_current_goals.redundant_to(
            self.seen_goals, self.seen_goals_nodes
        )
        redundant_to_str = (
            redundant_to.redundant_str() if redundant_to is not None else None
        )
        combined_tactics = ProofSearchTree.combine_tactics(
            parent_node.combined_model_tactics, attempted_tactic
        )
        valid_proof_steps = proof_check_result.valid_steps
        combined_proof_steps = parent_node.combined_proof_steps + valid_proof_steps
        tactic_str = ProofSearchTree.steps_to_str(valid_proof_steps)
        creation_time = time.time_ns() - search_start_time
        makes_progress = (
            redundant_to is None
            or self.__is_bullet(tactic_str)
            or self.__is_first_proof_tactic(
                parent_node.combined_proof_str(), tactic_str
            )
        )
        valid = True
        final_tactic = False
        new_leaf = ProofSearchTree(
            valid,
            final_tactic,
            makes_progress,
            valid_proof_steps,
            combined_proof_steps,
            attempted_tactic,
            combined_tactics,
            pretty_goal,
            parent_node.score.agg(score),
            creation_time,
            redundant_to_str=redundant_to_str,
        )
        return new_leaf

    def __filter_next_candidates(
        self,
        next_candidates: list[ProofSearchTree],
        next_goals: list[ParsedObligations],
    ) -> list[tuple[ProofSearchTree, ParsedObligations]]:
        mins: list[tuple[ProofSearchTree, ParsedObligations]] = []
        for candidate, goals in zip(next_candidates, next_goals):
            insert_new = True
            for i in range(len(mins)):
                cur_min_candidate, cur_min_goal = mins[i]
                if goals.as_hard_as(cur_min_goal):
                    insert_new = False
                    candidate.makes_progress = False
                    candidate.redundant_to_str = cur_min_candidate.redundant_str()
                    break
                if cur_min_goal.as_hard_as(goals):
                    insert_new = False
                    cur_min_candidate.makes_progress = False
                    cur_min_candidate.redundant_to_str = candidate.redundant_str()
                    mins[i] = (candidate, goals)
                    break
            if insert_new:
                mins.append((candidate, goals))
        return mins

    def search_step(
        self, step_num: int, search_start_time: int
    ) -> Optional[ProofSearchTree]:
        """If the search is completed, return the resulting node in
        the proof search tree."""
        leaf_subtree = heapq.heappop(self.frontier)
        leaf_subtree.set_expanded_num(step_num)
        example = self.__get_request_contents(
            leaf_subtree.combined_proof_steps, leaf_subtree.combined_model_tactics
        )
        start_time = time.time_ns()
        result = self.model_wrapper.get_recs(example, self.max_branch)
        end_time = time.time_ns()
        print(f"Model time: {(end_time - start_time) / 1e9}")
        children: list[ProofSearchTree] = []
        next_frontier_pool: list[ProofSearchTree] = []
        next_frontier_goals: list[ParsedObligations] = []
        for tactic, score in zip(result.next_tactic_list, result.score_list):
            proof_script = ProofSearchTree.combine_tactics(
                leaf_subtree.combined_model_tactics, tactic
            )
            proof_check_result = self.proof_manager.check_proof(
                proof_script, leaf_subtree.combined_proof_steps
            )
            node_score = self.score_type.from_unit_score(self.max_branch, score)
            match proof_check_result.tactic_result:
                case TacticResult.COMPLETE:
                    complete_node = self.__get_complete_child_node(
                        proof_check_result,
                        tactic,
                        leaf_subtree,
                        node_score,
                        search_start_time,
                    )
                    children.append(complete_node)
                    leaf_subtree.children = children
                    return complete_node

                case TacticResult.INVALID:
                    invalid_node = self.__get_invalid_child_node(
                        proof_check_result,
                        tactic,
                        leaf_subtree,
                        node_score,
                        search_start_time,
                    )
                    children.append(invalid_node)

                case TacticResult.VALID:
                    valid_node = self.__get_valid_child_node(
                        proof_check_result,
                        tactic,
                        leaf_subtree,
                        node_score,
                        search_start_time,
                    )
                    children.append(valid_node)
                    # We will check again if the candide makes progress to make
                    # sure it isn't superceded by later candidates.
                    if valid_node.makes_progress:
                        assert proof_check_result.parsed_current_goals is not None
                        next_frontier_pool.append(valid_node)
                        next_frontier_goals.append(
                            proof_check_result.parsed_current_goals
                        )

        for confirmed_next_candidate, confirmed_goals in self.__filter_next_candidates(
            next_frontier_pool, next_frontier_goals
        ):
            heapq.heappush(self.frontier, confirmed_next_candidate)
            self.seen_goals.append(confirmed_goals)
            self.seen_goals_nodes.append(confirmed_next_candidate)

        leaf_subtree.children = children
        return None

    @staticmethod
    def __is_first_proof_tactic(proof_script: str, tactic: str) -> bool:
        proof_pattern = r"Proof."
        proof_in_script = re.search(proof_pattern, proof_script) is not None
        proof_in_tactic = re.search(proof_pattern, tactic) is not None
        return proof_in_tactic and (not proof_in_script)

    @staticmethod
    def __is_bullet(tactic: str) -> bool:
        return re.search(r"\s+[-+*]+", tactic) is not None
