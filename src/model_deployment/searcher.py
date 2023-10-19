from __future__ import annotations
from typing import Optional, Any
from enum import Enum
import heapq
import pdb
import time
import re

import sys, os

from termcolor import colored

from tactic_gen.lm_example import LmExample
from model_deployment.model_wrapper import ModelWrapper, ModelResult
from model_deployment.node_score import NodeScore
from model_deployment.goal_comparer import NodeGoal
from model_deployment.proof_manager import ProofManager, TacticResult, ProofCheckResult

from coqlspclient.coq_file import CoqFile, GoalAnswer
from coqlspclient.coq_lsp_structs import Goal


class ProofSearchTree:
    uni_sideways_t = "\u251c"
    sideways_bar = "\u2500"
    uni_l = "\u2514"
    vert_bar = "\u2502"

    def __init__(
        self,
        valid: bool,
        final_tactic: bool,
        makes_progress: bool,
        valid_proof_steps: list[str],
        combined_proofs_steps: list[str],
        model_tactic: str,
        combined_model_tactics: str,
        goal: str,
        score: NodeScore,
        creation_time: int,
        expanded: Optional[int] = None,
        children: Optional[list[ProofSearchTree]] = None,
    ) -> None:
        assert type(valid) == bool
        assert type(final_tactic) == bool
        assert type(makes_progress) == bool
        assert type(valid_proof_steps) == list
        assert all([type(s) == str for s in valid_proof_steps])
        assert type(combined_proofs_steps) == list
        assert all([type(s) == str for s in combined_proofs_steps])
        assert type(goal) == str
        assert type(model_tactic) == str
        assert type(combined_model_tactics) == str
        assert isinstance(score, NodeScore)
        assert type(creation_time) == int
        assert expanded is None or type(expanded) == int
        self.valid = valid
        self.final_tactic = final_tactic
        self.makes_progress = makes_progress
        self.valid_proof_steps = valid_proof_steps
        self.combined_proof_steps = combined_proofs_steps
        self.model_tactic = model_tactic
        self.combined_model_tactics = combined_model_tactics
        self.goal = goal
        self.score = score
        self.creation_time = creation_time
        self.expanded = expanded
        if children is None:
            self.children = []
        else:
            assert type(children) == list
            assert all([type(c) == ProofSearchTree for c in children])
            self.children = children

    def combined_proof_str(self) -> str:
        return self.steps_to_str(self.combined_proof_steps)

    def steps_proof_str(self) -> str:
        return self.steps_to_str(self.valid_proof_steps)

    def __lt__(self, other: ProofSearchTree) -> bool:
        return other.score <= self.score

    def set_expanded_num(self, expanded_num: int) -> None:
        self.expanded = expanded_num

    def get_deepest_node(self, cur_depth: int = 0) -> tuple[ProofSearchTree, int]:
        cur_max_depth = cur_depth
        cur_deepest_node = self
        for child in self.children:
            child_deepest_node, depth = child.get_deepest_node(cur_depth + 1)
            if depth > cur_max_depth:
                cur_max_depth = depth
                cur_deepest_node = child_deepest_node
        return cur_deepest_node, cur_max_depth

    def pretty_print(
        self, start_marker: str = uni_l, indent: str = "", last_child: bool = True
    ) -> None:
        line_start = start_marker + (self.sideways_bar * 2) + " "
        start = indent + line_start
        step_str = self.steps_proof_str()
        clean_tactic = self.clean_tactic(step_str)
        clean_score = "{:7.6f}".format(self.score.compute())
        message = f"{start}{clean_score} {clean_tactic}"
        if self.expanded is not None and self.expanded > 0:
            expanded_len = len(str(self.expanded))
            message = message.replace(" " * expanded_len, str(self.expanded), 1)
        if not self.valid:
            message = colored(message, "red")
        elif self.final_tactic:
            message = colored(message, "green")
        elif not self.makes_progress:
            message = colored(message, "yellow")
        print(message)
        if last_child:
            new_indent = indent + " " * (len(line_start))
        else:
            new_indent = indent + self.vert_bar + " " * (len(line_start) - 1)

        for i, child in enumerate(self.children):
            if i < (len(self.children) - 1):
                start_marker = self.uni_sideways_t
                child.pretty_print(start_marker, new_indent, last_child=False)
            else:
                start_marker = self.uni_l
                child.pretty_print(start_marker, new_indent, last_child=True)

    def get_path_to_qed(self) -> list[ProofSearchTree]:
        if self.final_tactic:
            return [self]
        for child in self.children:
            child_return_path = child.get_path_to_qed()
            if len(child_return_path) > 0:
                return [self] + child_return_path
        return []

    def to_json(self) -> Any:
        return {
            "valid": self.valid,
            "final_tactic": self.final_tactic,
            "makes_progress": self.makes_progress,
            "valid_proof_steps": self.valid_proof_steps,
            "combined_proof_steps": self.combined_proof_steps,
            "model_tactic": self.model_tactic,
            "combined_model_tactics": self.combined_model_tactics,
            "goal": self.goal,
            "score": self.score.to_json(),
            "creation_time": self.creation_time,
            "expanded": self.expanded,
            "children": [c.to_json() for c in self.children],
        }

    @classmethod
    def from_json(cls, json_data: Any) -> ProofSearchTree:
        valid = json_data["valid"]
        final_tactic = json_data["final_tactic"]
        makes_progress = json_data["makes_progress"]
        valid_proof_steps = json_data["valid_proof_steps"]
        combined_proof_steps = json_data["combined_proof_steps"]
        model_tactic = json_data["model_tactic"]
        combined_model_tactics = json_data["combined_model_tactics"]
        goal = json_data["goal"]
        score = NodeScore.from_json(json_data["score"])
        creation_time = json_data["creation_time"]
        expanded = json_data["expanded"]
        children = [ProofSearchTree.from_json(c) for c in json_data["children"]]
        return cls(
            valid,
            final_tactic,
            makes_progress,
            valid_proof_steps,
            combined_proof_steps,
            model_tactic,
            combined_model_tactics,
            goal,
            score,
            creation_time,
            expanded,
            children,
        )

    @staticmethod
    def steps_to_str(steps: list[str]) -> str:
        return "".join(steps)

    @staticmethod
    def clean_tactic(tactic: str) -> str:
        return '"' + tactic.replace("\n", r"\n") + '"'

    @staticmethod
    def combine_tactics(tactic1: str, tactic2: str) -> str:
        if len(tactic1) == 0 or len(tactic2) == 0:
            return tactic1 + tactic2
        if re.match(r"\s", tactic2[0]):
            return tactic1 + tactic2
        if re.match(r"\s", tactic1[-1]):
            return tactic1 + tactic2
        return tactic1 + " " + tactic2


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
        node_goal = self.__get_goals(initial_check_result.current_goals)
        initial_score = score_type.get_initial_score()
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
        self.seen_goals: list[NodeGoal] = [node_goal]
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
    ) -> tuple[ProofSearchTree, NodeGoal]:
        assert proof_check_result.current_goals is not None
        assert proof_check_result.current_goals.goals is not None
        pretty_goal = repr(proof_check_result.current_goals.goals.goals)
        node_goal = self.__get_goals(proof_check_result.current_goals)
        goal_progress = node_goal.makes_progress(self.seen_goals)
        combined_tactics = ProofSearchTree.combine_tactics(
            parent_node.combined_model_tactics, attempted_tactic
        )
        valid_proof_steps = proof_check_result.valid_steps
        combined_proof_steps = parent_node.combined_proof_steps + valid_proof_steps
        tactic_str = ProofSearchTree.steps_to_str(valid_proof_steps)
        creation_time = time.time_ns() - search_start_time
        makes_progress = (
            goal_progress
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
        )
        return new_leaf, node_goal

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
        result = self.model_wrapper.get_recs(example, self.max_branch)
        children: list[ProofSearchTree] = []
        for tactic, score in zip(result.next_tactic_list, result.score_list):
            proof_script = ProofSearchTree.combine_tactics(
                leaf_subtree.combined_model_tactics, tactic
            )
            proof_check_result = self.proof_manager.check_proof(
                proof_script, leaf_subtree.combined_proof_steps
            )
            match proof_check_result.tactic_result:
                case TacticResult.COMPLETE:
                    complete_node = self.__get_complete_child_node(
                        proof_check_result,
                        tactic,
                        leaf_subtree,
                        score,
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
                        score,
                        search_start_time,
                    )
                    children.append(invalid_node)

                case TacticResult.VALID:
                    valid_node, node_goal = self.__get_valid_child_node(
                        proof_check_result,
                        tactic,
                        leaf_subtree,
                        score,
                        search_start_time,
                    )
                    children.append(valid_node)
                    if valid_node.makes_progress:
                        self.seen_goals.append(node_goal)
                        heapq.heappush(self.frontier, valid_node)
                        clean_steps = ProofSearchTree.clean_tactic(
                            valid_node.steps_proof_str()
                        )
                        clean_orig_step = ProofSearchTree.clean_tactic(tactic)
                        print(
                            f"adding new child node {clean_steps} from {clean_orig_step}"
                        )
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

    @staticmethod
    def __get_goals(goal_answer: GoalAnswer) -> NodeGoal:
        assert goal_answer.goals is not None
        fg_goals = goal_answer.goals.goals
        bg_goals: list[Goal] = []
        for goal_list1, goal_list2 in goal_answer.goals.stack:
            bg_goals.extend(goal_list1 + goal_list2)
        node_goal = NodeGoal(fg_goals + bg_goals)
        return node_goal
