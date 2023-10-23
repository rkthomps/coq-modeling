from __future__ import annotations
from typing import Optional, Any

import re

from model_deployment.node_score import NodeScore, CodeLLamaNodeScore
from termcolor import colored


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
        redundant_to_str: Optional[str] = None,
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
        self.redundant_to_str = redundant_to_str
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

    def redundant_str(self) -> str:
        return f"{self.model_tactic} with score {self.score.compute()}"

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
            assert self.redundant_to_str is not None
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
            "redundant_to_str": self.redundant_to_str,
        }

    @classmethod
    def eval_from_json(cls, json_data: Any) -> ProofSearchTree:
        final_tactic = json_data["final_tactic"]
        combined_model_tactics = json_data["combined_model_tactics"]
        creation_time = json_data["creation_time"]
        expanded = json_data["expanded"]
        children = [ProofSearchTree.eval_from_json(c) for c in json_data["children"]]

        # Default vars that don't matter for eval
        valid = True
        makes_progress = True
        valid_proof_steps: list[str] = []
        combined_proof_steps: list[str] = []
        model_tactic = ""
        goal = ""
        score = CodeLLamaNodeScore.get_initial_score(1)
        redundant_to_str = None

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
            redundant_to_str,
        )

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
        redundant_to_str = json_data["redundant_to_str"]
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
