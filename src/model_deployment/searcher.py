
from __future__ import annotations
from typing import Optional, Type, Any
import heapq 

import sys, os
import shutil

import jsonlines

from data_management.lm_example import LmExample 
from data_management.dataset_file import STEPS_NAME, FILE_CONTEXT_NAME, DatasetFile
from model_deployment.model_wrapper import ModelWrapper, ModelResult, NodeScore

from coqlspclient.coq_file import CoqFile
from coqlspclient.proof_state import ProofState, ProofTerm
from coqlspclient.coq_structs import Term
from coqlspclient.coq_structs import FileContext


def __proc_file_path(file_path: str) -> str:
    if file_path.startswith("/home"):
        return "/".join(file_path.split("/")[3:])
    return file_path


def __get_context(context: list[Term]) -> list[dict[str, Any]]:
    res = []
    for term in context:
        res.append({
            "text": term.text,
            "file_path": __proc_file_path(term.file_path),
            "module": term.module, 
            "type": str(term.type),
            "line": term.ast.range.start.line
        })
    return res


def __get_file_prefix(filename: str, search_token: str) -> Optional[str]:
    with open(filename, "r") as fin:
        file_contents = fin.read()
    token_idx = file_contents.find(search_token)
    if token_idx == -1:
        return None
    return file_contents[:token_idx]


def __get_fresh_path(dirname: str, fresh_base: str) -> str:
    name = fresh_base 
    while os.path.exists(os.path.join(dirname, name)):
        name += "_"
    return os.path.join(dirname, name)

def __get_last_proof_data_points(proof: ProofTerm) -> Any:
    data_points = []
    for i, step in enumerate(proof.steps):
        goals = list(map(lambda goal: repr(goal), step.goals.goals.goals))
        next_steps: list[dict[str, Any]] = []
        data_point = {
            "term": {
                "text": proof.text,
                "file_path": __proc_file_path(proof.file_path),
                "module": proof.module,
                "type": str(proof.type),
                "line": proof.ast.range.start.line,
                "context": __get_context(proof.context)
            },
            "step": {
                "text": step.text,
                "context": __get_context(step.context)
            },
            "n_step": i + 1,
            "goals": goals,
            "next_steps": next_steps 
        }
        for next_step in proof.steps[i + 1:]:
            next_steps.append({
                "text": next_step.text,
                "context": __get_context(next_step.context)
            })
        data_points.append(data_point)
    return data_points


class ProofSearchTree:
    def __init__(self, valid: bool):
        self.valid = valid
        self.score = 0 
        scores: list[float] = []
        tactics: list[str] = []
        children: list[ProofSearchTree] = []
    
    def __le__(self, other: ProofSearchTree) -> bool:
        return self.score >= other.score 


class SearchTreeManager:
    def __init__(self, file_path: str) -> None:
        self.searcher = Searcher(file_path)
        self.search_tree = ProofSearchTree(True)
        self.frontier: list[tuple[ProofSearchTree, list[str]]] = []
        empty_tac_list: list[str] = []
        heapq.heappush(self.frontier, (self.search_tree, empty_tac_list))

    def search_step(self) -> None: 
        leaf_subtree, leaf_path = heapq.heappop(self.frontier)


class Searcher:
    SEARCH_TOKEN = "<prove>"
    TIMEOUT = 60

    def __init__(self, file_path: str, 
                 example_type: Type[LmExample]) -> None:
        file_dir = os.path.dirname(file_path) 
        self.example_type = example_type
        self.__orig_file_path = file_path 
        self.__search_dir_path = __get_fresh_path(file_dir, ".proof-search")
        self.__hidden_file_path = __get_fresh_path(file_dir, os.path.basename(file_path))
        self.__file_prefix = __get_file_prefix(self.__orig_file_path, self.SEARCH_TOKEN)
        if self.__file_prefix is None:
            raise ValueError(f"Could not find search token {self.SEARCH_TOKEN}")
        print("Initiaizing Proof State")
        proof_state = self.__initialize_proof_state(self.__file_prefix, None)
        self.__cached_file_context = proof_state.coq_file.context


    def get_recs(self, tactics: list[str]) -> tuple[list[str], list[float]]:
        partial_proof_string = "".join(tactics)
        partial_proof_file = f"{self.__file_prefix}{partial_proof_string} Admitted."
        proof_state = self.__initialize_proof_state(partial_proof_file, self.__cached_file_context) 
        self.__update_search_dir(proof_state)
        dataset_obj = DatasetFile.from_directory(self.__search_dir_path)
        examples = self.example_type.from_dataset_file(dataset_obj)
        example = examples[-1]


    def __update_search_dir(self, proof_state: ProofState) -> None:
        last_proof = proof_state.proofs[-1]
        last_proof_data = __get_last_proof_data_points(last_proof)
        context_list = list(proof_state.context.terms.values())
        context_data = __get_context(context_list) 
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
                "file": __proc_file_path(last_proof.file_path),
                "context": context_data}])


    def __initialize_proof_state(self, contents: str, 
                                 context: Optional[FileContext]) -> ProofState:
        self.__update_hidden_file(contents)
        hidden_coq_file = CoqFile(self.__hidden_file_path, timeout=self.TIMEOUT) 
        return ProofState(hidden_coq_file)


    def __update_proof_state(self, contents: str) -> CoqFile:
        self.__update_hidden_file(contents)
        coq_file_obj = CoqFile(self.__hidden_file_path)
        return coq_file_obj


    def __update_hidden_file(self, contents: str) -> None:
        with open(self.__hidden_file_path, "w") as fout:
            fout.write(contents)


    def __enter__(self) -> None:
        pass


    def __exit__(self) -> None:
        pass


