from __future__ import annotations
from typing import Optional, Any
import heapq
import time
import re

import sys, os

from tactic_gen.lm_example import LmExample
from model_deployment.model_wrapper import ModelWrapper, ModelResult
from model_deployment.node_score import NodeScore
from model_deployment.goal_comparer import ParsedObligations
from model_deployment.proof_manager import ProofManager, TacticResult, ProofCheckResult
from model_deployment.search_tree import SearchNode, SearchTree

from data_management.dataset_file import DatasetFile, Proof

from typeguard import typechecked


@typechecked
class SuccessfulSearch:
    ALIAS = "success"

    def __init__(self, search_tree: SearchTree, qed_node: SearchNode) -> None:
        self.search_tree = search_tree
        self.qed_node = qed_node

    def get_proof(self) -> str:
        return self.qed_node.steps_to_str(self.qed_node.combined_proof_steps)

    def to_json(self) -> Any:
        return {
            "search_tree": self.search_tree.to_json(),
            "qed_node": self.qed_node.to_json(),
        }

    @classmethod
    def from_json(cls, json_data: Any) -> Any:
        search_tree = SearchTree.from_json(json_data["search_tree"])
        qed_node = SearchNode.from_json(json_data["qed_node"])
        return cls(search_tree, qed_node)


@typechecked
class FailedSearch:
    ALIAS = "failure"

    def __init__(self, search_tree: SearchTree) -> None:
        self.search_tree = search_tree

    def to_json(self) -> Any:
        return {"search_tree": self.search_tree.to_json()}

    @classmethod
    def from_json(cls, json_data: Any) -> Any:
        search_tree = SearchTree.from_json(json_data["search_tree"])
        return cls(search_tree)


@typechecked
class ErroredSearch:
    ALIAS = "error"

    def __init__(self, message: str, error_after: float) -> None:
        self.message = message
        self.error_after = error_after

    def to_json(self) -> Any:
        return {
            "message": self.message,
            "error_after": self.error_after,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> Any:
        return cls(json_data["message"], json_data["error_after"])


SearchResult = SuccessfulSearch | FailedSearch | ErroredSearch


def search_result_to_json(search_result: SearchResult) -> Any:
    return {"alias": search_result.ALIAS} | search_result.to_json()


def search_result_from_json(json_data: Any) -> SearchResult:
    match json_data["alias"]:
        case "success":
            return SuccessfulSearch.from_json(json_data)
        case "failure":
            return FailedSearch.from_json(json_data)
        case "error":
            return ErroredSearch.from_json(json_data)
        case a:
            raise ValueError(f"Unknown search result alias: f{a}")


@typechecked
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
        self.model_wrapper = model_wrapper
        self.proof_manager = proof_manager
        self.score_type = score_type
        self.max_branch = max_branch
        self.max_num_leaf_expansions = max_num_leaf_expansions
        self.timeout = timeout
        initial_validity = True
        final_tactic = False
        makes_progress = True
        initial_tactic: str = ""
        combined_valid_steps: list[str] = []
        initial_proof = SearchNode.steps_to_str(combined_valid_steps)
        initial_check_result = proof_manager.check_proof(initial_proof)
        assert initial_check_result.tactic_result == TacticResult.VALID
        assert initial_check_result.current_goals is not None
        assert initial_check_result.dataset_file is not None
        initial_score = self.score_type.get_initial_score(max_branch)
        creation_time = -1
        self.root = SearchNode(
            initial_validity,
            final_tactic,
            makes_progress,
            initial_tactic,
            combined_valid_steps,
            initial_score,
            creation_time,
            initial_check_result.dataset_file.proofs[-1],
        )
        self.search_tree = SearchTree(
            initial_check_result.dataset_file.file_context, self.root
        )
        self.frontier: list[SearchNode] = []
        self.seen_goals: list[ParsedObligations] = []
        self.seen_goals_nodes: list[SearchNode] = []
        heapq.heappush(self.frontier, self.root)

    def search(self, print_trees: bool = False) -> SuccessfulSearch | FailedSearch:
        start = time.time_ns()
        for i in range(self.max_num_leaf_expansions):
            cur = time.time_ns()
            if ((cur - start) / 1e9) > self.timeout:
                break
            if len(self.frontier) == 0:
                break
            print(f"Beginning iteration {i + 1} of search.")
            possible_complete_node = self.search_step(i, start)
            if print_trees:
                self.search_tree.pretty_print(verbose=True)
            if possible_complete_node:
                return SuccessfulSearch(self.search_tree, possible_complete_node)
        return FailedSearch(self.search_tree)

    def __get_complete_child_node(
        self,
        proof_check_result: ProofCheckResult,
        attempted_tactic: str,
        parent_node: SearchNode,
        score: NodeScore,
        search_start_time: int,
    ) -> SearchNode:
        assert proof_check_result.current_goals is not None
        assert proof_check_result.current_goals.goals is not None
        assert proof_check_result.current_goals.goals.goals == []
        valid = True
        final_tactic = True
        makes_progress = True
        creation_time = time.time_ns() - search_start_time
        proof = self.__get_possible_last_proof(proof_check_result.dataset_file)
        complete_node = SearchNode(
            valid,
            final_tactic,
            makes_progress,
            attempted_tactic,
            proof_check_result.attempted_steps,
            parent_node.score.agg(score),
            creation_time,
            proof,
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
        proof = self.__get_possible_last_proof(proof_check_result.dataset_file)
        invalid_node = SearchNode(
            valid,
            final_tactic,
            makes_progress,
            attempted_tactic,
            combined_steps,
            parent_node.score.agg(score),
            creation_time,
            proof,
        )
        return invalid_node

    def __get_valid_child_node(
        self,
        proof_check_result: ProofCheckResult,
        attempted_tactic: str,
        parent_node: SearchNode,
        score: NodeScore,
        search_start_time: int,
    ) -> SearchNode:
        assert proof_check_result.current_goals is not None
        assert proof_check_result.current_goals.goals is not None
        assert proof_check_result.parsed_current_goals is not None
        redundant_to = proof_check_result.parsed_current_goals.redundant_to(
            self.seen_goals, self.seen_goals_nodes
        )
        redundant_to_str = (
            redundant_to.redundant_str() if redundant_to is not None else None
        )
        valid_proof_steps = proof_check_result.attempted_steps
        tactic_str = SearchNode.steps_to_str(valid_proof_steps)
        creation_time = time.time_ns() - search_start_time
        makes_progress = (
            redundant_to is None
            or self.__is_bullet(tactic_str)
            or self.__is_first_proof_tactic(parent_node.total_proof_str(), tactic_str)
        )
        proof = self.__get_possible_last_proof(proof_check_result.dataset_file)
        assert proof is not None
        valid = True
        final_tactic = False
        new_leaf = SearchNode(
            valid,
            final_tactic,
            makes_progress,
            attempted_tactic,
            proof_check_result.attempted_steps,
            parent_node.score.agg(score),
            creation_time,
            proof,
            redundant_to_str=redundant_to_str,
        )
        return new_leaf

    def __filter_next_candidates(
        self,
        next_candidates: list[SearchNode],
        next_goals: list[ParsedObligations],
    ) -> list[tuple[SearchNode, ParsedObligations]]:
        mins: list[tuple[SearchNode, ParsedObligations]] = []
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
    ) -> Optional[SearchNode]:
        """If the search is completed, return the resulting node in
        the proof search tree."""
        leaf_subtree = heapq.heappop(self.frontier)
        leaf_subtree.set_expanded_num(step_num)
        assert leaf_subtree.proof is not None
        dset_file = DatasetFile(self.search_tree.file_context, [leaf_subtree.proof])
        example = self.proof_manager.get_example(dset_file)
        start_time = time.time_ns()
        result = self.model_wrapper.get_recs(example, self.max_branch)
        end_time = time.time_ns()
        print(f"Model time: {(end_time - start_time) / 1e9}")
        children: list[SearchNode] = []
        next_frontier_pool: list[SearchNode] = []
        next_frontier_goals: list[ParsedObligations] = []
        for tactic, score, num_tokens in zip(
            result.next_tactic_list, result.score_list, result.num_tokens_list
        ):
            proof_script = leaf_subtree.total_proof_str() + tactic
            start_time = time.time_ns()
            proof_check_result = self.proof_manager.check_proof(proof_script)
            end_time = time.time_ns()
            print(f"Check time: {(end_time - start_time) / 1e9}")
            node_score = self.score_type.from_unit_score(
                score, num_tokens, self.max_branch
            )
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

        filtered_candidates = self.__filter_next_candidates(
            next_frontier_pool, next_frontier_goals
        )
        for confirmed_next_candidate, confirmed_goals in filtered_candidates:
            heapq.heappush(self.frontier, confirmed_next_candidate)
            self.seen_goals.append(confirmed_goals)
            self.seen_goals_nodes.append(confirmed_next_candidate)

        leaf_subtree.children = children
        return None

    @staticmethod
    def __get_possible_last_proof(
        dataset_file: Optional[DatasetFile],
    ) -> Optional[Proof]:
        match dataset_file:
            case None:
                return None
            case _:
                return dataset_file.proofs[-1]

    @staticmethod
    def __is_first_proof_tactic(proof_script: str, tactic: str) -> bool:
        proof_pattern = r"Proof."
        proof_in_script = re.search(proof_pattern, proof_script) is not None
        proof_in_tactic = re.search(proof_pattern, tactic) is not None
        return proof_in_tactic and (not proof_in_script)

    @staticmethod
    def __is_bullet(tactic: str) -> bool:
        return re.search(r"\.\s+[-+*]+", tactic) is not None
