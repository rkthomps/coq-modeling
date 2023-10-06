
from __future__ import annotations
from typing import Optional, Any
from types import TracebackType
from enum import Enum
import heapq 
import time
import re

import sys, os
import shutil

import jsonlines
from termcolor import colored

from tactic_gen.lm_example import LmExample
from data_management.create_lm_dataset import LmExampleConfig
from data_management.dataset_file import STEPS_NAME, FILE_CONTEXT_NAME, DatasetFile
from model_deployment.model_wrapper import ModelWrapper, ModelResult
from model_deployment.node_score import NodeScore
from model_deployment.goal_comparer import NodeGoal

from coqlspclient.coq_file import CoqFile, GoalAnswer
from coqlspclient.coq_lsp_structs import Goal
from coqlspclient.proof_state import ProofState, ProofTerm
from coqlspclient.coq_structs import Term
from coqlspclient.coq_structs import FileContext


def proc_file_path(file_path: str) -> str:
    if file_path.startswith("/home"):
        return "/".join(file_path.split("/")[3:])
    return file_path


def get_context(context: list[Term]) -> list[dict[str, Any]]:
    res = []
    for term in context:
        res.append({
            "text": term.text,
            "file_path": proc_file_path(term.file_path),
            "module": term.module, 
            "type": str(term.type),
            "line": term.ast.range.start.line
        })
    return res


def get_file_prefix(filename: str, search_token: str) -> Optional[str]:
    with open(filename, "r") as fin:
        file_contents = fin.read()
    token_idx = file_contents.find(search_token)
    if token_idx == -1:
        return None
    return file_contents[:token_idx]


def get_fresh_path(dirname: str, fresh_base: str) -> str:
    name = fresh_base 
    while os.path.exists(os.path.join(dirname, name)):
        name = "_" + name
    return os.path.join(dirname, name)

def get_last_proof_data_points(proof: ProofTerm) -> Any:
    data_points = []
    for i, step in enumerate(proof.steps):
        goals = list(map(lambda goal: repr(goal), step.goals.goals.goals))
        next_steps: list[dict[str, Any]] = []
        data_point = {
            "term": {
                "text": proof.text,
                "file_path": proc_file_path(proof.file_path),
                "module": proof.module,
                "type": str(proof.type),
                "line": proof.ast.range.start.line,
                "context": get_context(proof.context)
            },
            "step": {
                "text": step.text,
                "context": get_context(step.context)
            },
            "n_step": i + 1,
            "goals": goals,
            "next_steps": next_steps 
        }
        for next_step in proof.steps[i + 1:]:
            next_steps.append({
                "text": next_step.text,
                "context": get_context(next_step.context)
            })
        data_points.append(data_point)
    return data_points


class ProofSearchTree:
    uni_sideways_t = u"\u251c"
    sideways_bar = u"\u2500"
    uni_l = u"\u2514"
    vert_bar = u"\u2502"

    def __init__(self, valid: bool, final_tactic: bool, makes_progress: bool,
                 tactic: str, combined_tactics: str, goal: str, score: NodeScore) -> None:
        assert type(valid) == bool
        assert type(final_tactic) == bool
        assert type(makes_progress) == bool
        assert type(tactic) == str
        assert type(combined_tactics) == str
        assert type(goal) == str
        assert isinstance(score, NodeScore) 
        self.valid = valid
        self.final_tactic = final_tactic
        self.makes_progress = makes_progress
        self.tactic = tactic
        self.combined_tactics = combined_tactics
        self.goal = goal
        self.score = score 
        self.expanded: Optional[int] = None
        self.children: list[ProofSearchTree] = []

    
    def __lt__(self, other: ProofSearchTree) -> bool:
        return other.score <= self.score


    def set_expanded_num(self, expanded_num: int) -> None:
        self.expanded = expanded_num


    def pretty_print(self, start_marker: str=uni_l, indent: str="", 
                     last_child: bool=True) -> None:
        line_start = start_marker + (self.sideways_bar * 2) + " "
        start = indent + line_start 
        clean_tactic = self.__clean_tactic(self.tactic)
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
            new_indent = indent + " "  * (len(line_start))
        else:
            new_indent = indent + self.vert_bar + " " * (len(line_start) - 1)

        for i, child in enumerate(self.children):
            if i < (len(self.children) - 1):
                start_marker = self.uni_sideways_t
                child.pretty_print(start_marker, new_indent, last_child=False)
            else:
                start_marker = self.uni_l
                child.pretty_print(start_marker, new_indent, last_child=True)


    def to_json(self) -> Any:
        return {
            "valid": self.valid,
            "final_tactic": self.final_tactic,
            "makes_progress": self.makes_progress,
            "tactic": self.tactic,
            "combined_tactics": self.combined_tactics,
            "goal": self.goal,
            "score": self.score.to_json(),
        }

    @classmethod
    def from_json(cls, json_data: Any) -> ProofSearchTree:
        valid = json_data["valid"]
        final_tactic = json_data["final_tactic"]
        makes_progress = json_data["makes_progress"]
        tactic = json_data["tactic"]
        combined_tactics = json_data["combined_tactics"]
        goal = json_data["goal"]
        score = NodeScore.from_json(json_data["score"])
        return cls(valid, final_tactic, makes_progress, tactic,
                   combined_tactics, goal, score)

    @staticmethod
    def __clean_tactic(tactic: str) -> str:
        return "\"" + tactic.replace("\n", r"\n") + "\""


class SearchResult:
    def __init__(self, search_tree: ProofSearchTree,
                 qed_node: Optional[ProofSearchTree]) -> None:
        self.search_tree = search_tree
        self.qed_node = qed_node

    def found_proof(self) -> bool:
        return self.qed_node is not None

    def get_proof(self) -> str:
        if not self.found_proof():
            raise ValueError("Search did not yeild proof.")
        assert self.qed_node is not None
        return self.qed_node.combined_tactics


class SearchTreeManager:
    def __init__(self, 
                 model_wrapper: ModelWrapper, 
                 proof_manager: ProofManager,
                 score_type: type[NodeScore],
                 max_branch: int,
                 max_num_leaf_expansions: int,
                 timeout: int) -> None:
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
        initial_tactic = ""
        combined_tactics = ""
        initial_goal = ""
        initial_tactic_result, goals = proof_manager.check_proof(combined_tactics)
        assert initial_tactic_result == TacticResult.VALID
        assert goals is not None
        node_goal = self.__get_goals(goals)
        initial_score = score_type.get_initial_score() 
        self.search_tree = ProofSearchTree(
            initial_validity, final_tactic, makes_progress, initial_tactic, 
            combined_tactics, initial_goal, initial_score)
        self.frontier: list[ProofSearchTree] = []
        self.seen_goals: list[NodeGoal] = [node_goal]
        heapq.heappush(self.frontier, self.search_tree)


    def __get_request_contents(self, partial_proof: str) -> LmExample:
        return self.proof_manager.get_example(partial_proof)


    def search(self) -> SearchResult:
        start = time.time_ns()
        for i in range(self.max_num_leaf_expansions):
            cur = time.time_ns()
            if ((cur - start) / 1e9) > self.timeout:
                break
            if len(self.frontier) == 0:
                break
            print(f"Beginning iteration {i + 1} of search.")
            possible_complete_node = self.search_step(i)
            self.search_tree.pretty_print()
            if possible_complete_node is not None:
                return SearchResult(self.search_tree, possible_complete_node)
        return SearchResult(self.search_tree, None)


    def search_step(self, step_num: int) -> Optional[ProofSearchTree]: 
        """If the search is completed, return the resulting node in
           the proof search tree."""
        leaf_subtree = heapq.heappop(self.frontier)
        leaf_subtree.set_expanded_num(step_num)
        example = self.__get_request_contents(leaf_subtree.combined_tactics)
        result = self.model_wrapper.get_recs(example, self.max_branch)
        children: list[ProofSearchTree] = []
        for tactic, score in zip(result.next_tactic_list, result.score_list):
            proof_script = leaf_subtree.combined_tactics + " " + tactic
            tactic_result, goals = self.proof_manager.check_proof(proof_script) 
            if tactic_result == TacticResult.COMPLETE:
                assert goals is None
                pretty_goal = "complete"
                valid = True
                final_tactic = True
                makes_progress = True 
                complete_node = ProofSearchTree(
                    valid, final_tactic, makes_progress, tactic, proof_script,
                    pretty_goal, leaf_subtree.score.agg(score)
                )
                children.append(complete_node)
                leaf_subtree.children = children
                return complete_node
            if tactic_result == TacticResult.INVALID:
                assert goals is None
                valid = False
                final_tactic = False
                makes_progress = False
                pretty_goal = "error"
                children.append(ProofSearchTree(
                    valid, final_tactic, makes_progress, tactic, proof_script, 
                    pretty_goal, leaf_subtree.score.agg(score)
                ))
            if tactic_result == TacticResult.VALID:
                assert goals is not None
                pretty_goal = repr(goals.goals.goals)
                node_goal = self.__get_goals(goals) 
                goal_progress = node_goal.makes_progress(self.seen_goals)
                proof_in_tactic = re.search
                makes_progress = (
                    goal_progress or 
                    self.__is_bullet(tactic) or 
                    self.__is_first_proof_tactic(leaf_subtree.combined_tactics, tactic))
                valid = True
                final_tactic = False
                new_leaf = ProofSearchTree(
                    valid, final_tactic, makes_progress, tactic, proof_script, 
                    pretty_goal, leaf_subtree.score.agg(score))
                children.append(new_leaf)
                if makes_progress:
                    self.seen_goals.append(node_goal)
                    heapq.heappush(self.frontier, new_leaf)
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
        fg_goals = goal_answer.goals.goals
        bg_goals: list[Goal] = []
        for goal_list1, goal_list2 in goal_answer.goals.stack:
            bg_goals.extend(goal_list1 + goal_list2)
        node_goal = NodeGoal(fg_goals + bg_goals) 
        return node_goal



class TacticResult(Enum):
    COMPLETE = 1
    VALID = 2
    INVALID = 3


class ProofManager:
    SEARCH_TOKEN = "<prove>"
    TIMEOUT = 60

    def __init__(self, file_path: str, lm_example_config: LmExampleConfig) -> None:
        file_dir = os.path.dirname(file_path) 
        self.example_type = lm_example_config.format_type
        self.premise_wrapper = lm_example_config.premise_wrapper
        self.__orig_file_path = file_path 
        self.__search_dir_path = get_fresh_path(file_dir, ".proof-search")
        self.__hidden_file_path = get_fresh_path(file_dir, os.path.basename(file_path))
        self.__file_prefix = get_file_prefix(self.__orig_file_path, self.SEARCH_TOKEN)
        if self.__file_prefix is None:
            raise ValueError(f"Could not find search token {self.SEARCH_TOKEN}")
        print("Initiaizing Proof State")
        self.__update_hidden_file(f"{self.__file_prefix} Admitted.")
        with CoqFile(self.__hidden_file_path, timeout=self.TIMEOUT) as coq_file:
            with ProofState(coq_file, None) as proof_state:
                self.__cached_file_context = proof_state.coq_file.context


    def check_proof(self, partial_proof: str
                    ) -> tuple[TacticResult, Optional[GoalAnswer]]:
        if ("Admitted." in partial_proof) or ("admit." in partial_proof):
            return TacticResult.INVALID, None
        partial_proof_file = f"{self.__file_prefix}{partial_proof}"
        self.__update_hidden_file(partial_proof_file)
        with CoqFile(self.__hidden_file_path, timeout=self.TIMEOUT) as hidden_coq_file:
            hidden_coq_file.run()
            if not hidden_coq_file.is_valid:
                return TacticResult.INVALID, None
            if not hidden_coq_file.in_proof:
                return TacticResult.COMPLETE, None
            return TacticResult.VALID, hidden_coq_file.current_goals()


    def get_example(self, partial_proof: str) -> LmExample:
        partial_proof_file = f"{self.__file_prefix}{partial_proof} Admitted."
        self.__update_hidden_file(partial_proof_file)
        time1 = time.time_ns()
        with CoqFile(self.__hidden_file_path, timeout=self.TIMEOUT) as coq_file:
            time2 = time.time_ns()
            with ProofState(coq_file, self.__cached_file_context) as proof_state:
                time3 = time.time_ns()
                print(f"Coqfile: {(time2 - time1) / 1e9}; State: {(time3 - time2) / 1e9}")
                self.__update_search_dir(proof_state)
                dataset_obj = DatasetFile.from_directory(self.__search_dir_path)
                examples = self.example_type.from_dataset_file(dataset_obj, self.premise_wrapper)
                example = examples[-1]
                return example


    def get_dataset_file(self, partial_proof: str) -> DatasetFile:
        partial_proof_file = f"{self.__file_prefix}{partial_proof} Admitted."
        self.__update_hidden_file(partial_proof_file)
        time1 = time.time_ns()
        with CoqFile(self.__hidden_file_path, timeout=self.TIMEOUT) as coq_file:
            time2 = time.time_ns()
            with ProofState(coq_file, self.__cached_file_context) as proof_state:
                time3 = time.time_ns()
                print(f"Coqfile: {(time2 - time1) / 1e9}; State: {(time3 - time2) / 1e9}")
                self.__update_search_dir(proof_state)
                dataset_obj = DatasetFile.from_directory(self.__search_dir_path)
                return dataset_obj


    def __update_search_dir(self, proof_state: ProofState) -> None:
        last_proof = proof_state.proofs[-1]
        last_proof_data = get_last_proof_data_points(last_proof)
        context_list = list(proof_state.context.terms.values())
        context_data = get_context(context_list) 
        steps_loc = os.path.join(self.__search_dir_path, STEPS_NAME)
        context_loc = os.path.join(self.__search_dir_path, FILE_CONTEXT_NAME)
        if not os.path.exists(self.__search_dir_path):
            os.makedirs(self.__search_dir_path)
        if os.path.exists(steps_loc):
            os.remove(steps_loc)
        if os.path.exists(context_loc):
            os.remove(context_loc)
        
        with jsonlines.open(steps_loc, "w") as fout:
            fout.write_all(last_proof_data)
        with jsonlines.open(context_loc, "w") as fout:
            fout.write_all([{
                "file": proc_file_path(last_proof.file_path),
                "context": context_data}])


    def __update_hidden_file(self, contents: str) -> None:
        with open(self.__hidden_file_path, "w") as fout:
            fout.write(contents)
        
    def __enter__(self) -> ProofManager:
        return self

    def __exit__(self, exc_type: type[BaseException], 
                 exc_value: BaseException | None, 
                 traceback: TracebackType | None) -> None:
        self.close()

    def close(self) -> None:
        shutil.rmtree(self.__search_dir_path)
        os.remove(self.__hidden_file_path)


