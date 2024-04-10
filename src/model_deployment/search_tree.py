from __future__ import annotations
from typing import Optional, Any
from dataclasses import dataclass

import re

from data_management.dataset_file import FileContext, Proof
from data_management.sentence_db import SentenceDB
from model_deployment.node_score import NodeScore
from model_deployment.mine_goals import GoalRecord
from termcolor import colored


class SearchTree:
    def __init__(self, file_contex: FileContext, root: SearchNode) -> None:
        self.file_context = file_contex
        self.root = root

    def pretty_print(
        self,
        verbose: bool = True,
    ) -> None:
        self.root.pretty_print(verbose=verbose)

    def to_json(self, sentences_db: SentenceDB) -> Any:
        return {
            "file_context": self.file_context.to_jsonlines(sentences_db, False),
            "root": self.root.to_json(sentences_db),
        }

    @classmethod
    def from_json(cls, json_data: Any, sentence_db: SentenceDB) -> SearchTree:
        file_context = FileContext.context_from_lines(
            json_data["file_context"], sentence_db
        )
        root = SearchNode.from_json(json_data["root"], sentence_db)
        return cls(file_context, root)


class SearchNode:
    uni_sideways_t = "\u251c"
    sideways_bar = "\u2500"
    uni_l = "\u2514"
    vert_bar = "\u2502"

    def __init__(
        self,
        valid: bool,
        final_tactic: bool,
        makes_progress: bool,
        model_tactic: str,
        combined_proofs_steps: list[str],
        score: NodeScore,
        creation_time: int,
        proof: Optional[Proof],
        goal_record: Optional[GoalRecord],
        expanded: Optional[int] = None,
        model_input: Optional[str] = None,
        children: Optional[list[SearchNode]] = None,
        redundant_to_str: Optional[str] = None,
        depth: Optional[int] = None,
    ) -> None:
        self.valid = valid
        self.final_tactic = final_tactic
        self.makes_progress = makes_progress
        self.model_tactic = model_tactic
        self.combined_proof_steps = combined_proofs_steps
        self.score = score
        self.creation_time = creation_time
        self.proof = proof
        self.goal_record = goal_record
        self.expanded = expanded
        self.model_input = model_input
        self.redundant_to_str = redundant_to_str
        if children is None:
            self.children = []
        else:
            self.children = children
        self.depth = depth

    def total_proof_str(self) -> str:
        return self.steps_to_str(self.combined_proof_steps)

    def __lt__(self, other: SearchNode) -> bool:
        return other.score <= self.score

    def set_expanded_num(self, expanded_num: int) -> None:
        self.expanded = expanded_num

    def set_model_input(self, model_input: str) -> None:
        self.model_input = model_input

    def redundant_str(self) -> str:
        return f"{self.model_tactic} with score {self.score.compute()}"

    def get_last_node_time(self) -> float:
        my_creation_time = self.creation_time
        subtree_max_creation_times = [c.get_last_node_time() for c in self.children]
        return max([my_creation_time] + subtree_max_creation_times)

    def __get_last_node_expanded(self) -> Optional[int]:
        if self.expanded is None:
            return None
        child_max_expanded: int = self.expanded
        for c in self.children:
            c_expanded = c.__get_last_node_expanded()
            if c_expanded is not None and child_max_expanded < c_expanded:
                child_max_expanded = c_expanded
        return child_max_expanded

    def get_last_node_expanded(self) -> int:
        max_expanded = self.__get_last_node_expanded()
        if max_expanded is None:
            return 0
        return max_expanded

    def size(self) -> int:
        return 1 + sum([c.size() for c in self.children])

    def num_errors(self) -> int:
        self_error = 0 if self.valid else 1
        return self_error + sum([c.num_errors() for c in self.children])

    def num_pruned(self) -> int:
        self_pruned = 1 if not self.makes_progress and self.valid else 0
        return self_pruned + sum([c.num_pruned() for c in self.children])

    def __get_deepest_node(self, cur_depth: int) -> tuple[SearchNode, int]:
        cur_max_depth = cur_depth
        cur_deepest_node = self
        for child in self.children:
            child_deepest_node, depth = child.__get_deepest_node(cur_depth + 1)
            if cur_max_depth < depth:
                cur_max_depth = depth
                cur_deepest_node = child_deepest_node
        return cur_deepest_node, cur_max_depth

    def get_deepest_node(self) -> tuple[SearchNode, int]:
        return self.__get_deepest_node(0)

    def pretty_print(
        self,
        start_marker: str = uni_l,
        indent: str = "",
        last_child: bool = True,
        verbose: bool = True,
    ) -> None:
        line_start = start_marker + (self.sideways_bar * 2) + " "
        start = indent + line_start
        clean_tactic = self.clean_tactic(self.model_tactic)
        if verbose:
            clean_score = "{:7.6f}".format(self.score.compute())
            message = f"{start}{clean_score} {clean_tactic}"
        else:
            message = f"{start}{clean_tactic}"
        if self.expanded is not None and self.expanded > 0:
            expanded_len = len(str(self.expanded))
            message = message.replace(" " * expanded_len, str(self.expanded), 1)
        if not self.valid:
            message = colored(message, "red")
        elif self.final_tactic:
            message = colored(message, "green")
        elif not self.makes_progress:
            assert self.redundant_to_str is not None
            if verbose:
                message = message + f" redundant to {self.redundant_to_str}"
            message = colored(message, "yellow")
        print(message)
        if last_child:
            new_indent = indent + " " * (len(line_start))
        else:
            new_indent = indent + self.vert_bar + " " * (len(line_start) - 1)

        for i, child in enumerate(self.children):
            if i < (len(self.children) - 1):
                start_marker = self.uni_sideways_t
                child.pretty_print(
                    start_marker, new_indent, last_child=False, verbose=verbose
                )
            else:
                start_marker = self.uni_l
                child.pretty_print(
                    start_marker, new_indent, last_child=True, verbose=verbose
                )

    def get_path_to_qed(self) -> list[SearchNode]:
        if self.final_tactic:
            return [self]
        for child in self.children:
            child_return_path = child.get_path_to_qed()
            if len(child_return_path) > 0:
                return [self] + child_return_path
        return []

    def to_json(self, sentences_db: SentenceDB) -> Any:
        return {
            "valid": self.valid,
            "final_tactic": self.final_tactic,
            "makes_progress": self.makes_progress,
            "model_tactic": self.model_tactic,
            "combined_proof_steps": self.combined_proof_steps,
            "score": self.score.to_json(),
            "creation_time": self.creation_time,
            "proof": (
                self.proof.to_json(sentences_db, False) if self.proof else self.proof
            ),
            "goal_record": self.goal_record.to_json() if self.goal_record else None,
            "expanded": self.expanded,
            "model_input": self.model_input,
            "redundant_to_str": self.redundant_to_str,
            "children": [c.to_json(sentences_db) for c in self.children],
        }

    @classmethod
    def from_json(cls, json_data: Any, sentences_db: SentenceDB) -> SearchNode:
        valid = json_data["valid"]
        final_tactic = json_data["final_tactic"]
        makes_progress = json_data["makes_progress"]
        model_tactic = json_data["model_tactic"]
        combined_proof_steps = json_data["combined_proof_steps"]
        score = NodeScore.from_json(json_data["score"])
        creation_time = json_data["creation_time"]
        proof_data = json_data["proof"]
        proof = Proof.from_json(proof_data, sentences_db) if proof_data else proof_data

        if "goal_record" in json_data and json_data["goal_record"] is not None:
            goal_record = GoalRecord.from_json(json_data["goal_record"])
        else:
            goal_record = None

        expanded = json_data["expanded"]
        model_input = json_data["model_input"] if "model_input" in json_data else None
        children = [
            SearchNode.from_json(c, sentences_db) for c in json_data["children"]
        ]
        redundant_to_str = json_data["redundant_to_str"]
        return cls(
            valid,
            final_tactic,
            makes_progress,
            model_tactic,
            combined_proof_steps,
            score,
            creation_time,
            proof,
            goal_record,
            expanded,
            model_input,
            children,
            redundant_to_str,
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
