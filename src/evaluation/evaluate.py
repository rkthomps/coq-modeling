
from __future__ import annotations
from typing import Any, Iterable
import json
import sys, os
import argparse
import random
import shutil
import time
import traceback


from coqlspclient.coq_file import CoqFile 
from coqlspclient.proof_file import ProofFile
from coqlspclient.coq_lsp_structs import Position

from tactic_gen.lm_example import LmExample, LMEXAMPLE_ALIASES
from data_management.split_raw_data import SPLITS, assignment_shape_expected
from data_management.create_lm_dataset import LmExampleConfig
from model_deployment.searcher import SearchTreeManager, ProofSearchTree, SearchResult
from model_deployment.proof_manager import (
    ProofManager, SEARCH_TOKEN, hidden_files_from_prefix, ProofCheckResult, TacticResult)
from model_deployment.model_wrapper import ModelWrapper, MODEL_WRAPPER_ALIASES 
from model_deployment.node_score import NodeScore, NODE_SCORE_ALIASES
from evaluation.impose_file_hierarchy import mapping_shape_correct, FILE_MAPPING_NAME, DESIRED_PREFIX

from tqdm import tqdm
from yaml import load, Loader 


class EvalSearchResult:
    def __init__(self, search_result: SearchResult, 
                 orig_file_path: str,
                 proof_prefix: str) -> None:
        assert type(search_result) == SearchResult
        assert type(orig_file_path) == str
        assert type(proof_prefix) == str
        self.search_result = search_result
        self.orig_file_path = orig_file_path
        self.proof_prefix = proof_prefix 

    def to_json(self) -> Any:
        return {
            "search_result": self.search_result.to_json(), 
            "orig_file_path": self.orig_file_path,
            "proof_prefix": self.proof_prefix,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> EvalSearchResult:
        search_result_data = json_data["search_result"]
        search_result = SearchResult.from_json(search_result_data)
        orig_file_path = json_data["orig_file_path"]
        proof_prefix = json_data["proof_prefix"]
        return cls(search_result, orig_file_path, proof_prefix)


# Need a proof
class Evaluator:
    def __init__(self, 
                 assignment_loc: str, 
                 results_loc: str,
                 file_tree_loc: str,
                 split: str, 
                 timeout: int, 
                 num_proofs: int, 
                 branching_factor: int,
                 max_leaf_expansions: int,
                 model_wrapper: ModelWrapper,
                 node_score_type: type[NodeScore],
                 example_type: type[LmExample],
                 coq_file_timeout: int=60,
                 ) -> None:
        assert type(assignment_loc) == str
        assert type(results_loc) == str
        assert type(split) == str
        assert type(timeout) == int
        assert type(num_proofs) == int
        assert type(max_leaf_expansions) ==int
        assert type(branching_factor) == int
        assert isinstance(model_wrapper, ModelWrapper)
        assert type(node_score_type) == type 
        assert type(example_type) == type
        self.assignments_loc = assignment_loc
        self.results_loc = results_loc
        self.file_tree_loc = file_tree_loc
        self.split = split
        self.timeout = timeout
        self.num_proofs = num_proofs
        self.branching_factor = branching_factor
        self.max_leaf_expansions = max_leaf_expansions
        self.model_wrapper = model_wrapper 
        self.example_type = example_type
        self.node_score_type = node_score_type
        self.coq_file_timeout = coq_file_timeout


    def proof_generator(self) -> Iterable[tuple[str, str, str, str]]:
        with open(self.assignments_loc, "r") as fin:
            assignment = json.load(fin)
        assert assignment_shape_expected(assignment)
        mapping_loc = os.path.join(self.file_tree_loc, FILE_MAPPING_NAME)
        with open(mapping_loc, "r") as fin:
            mapping = json.load(fin) 
        assert mapping_shape_correct(mapping)
        assert self.split in SPLITS
        #eligible_files = assignment[self.split]
        eligible_files = [
            "-coq-dataset-repos-voellinger-verified-certifying-distributed-algorithms-shortest-path-problem-arg_min_inequ.v",
            "-coq-dataset-repos-voellinger-verified-certifying-distributed-algorithms-shortest-path-problem-minimal_existence.v",
            "-coq-dataset-repos-coq-community-jmlcoq-theories-ListHelpers.v",
            "-coq-dataset-repos-anshumanmohan-CertiGraph-VST-VST-floyd-simple_reify.v",
            "-coq-dataset-repos-airxhi-CompCert-lib-Axioms.v",
        ]
        all_proof_prefixes: list[tuple[str, str]] = []
        print("Indexing Proofs...")
        for file in tqdm(eligible_files):
            physical_path = mapping[file]
            with open(physical_path, "r") as fin:
                contents = fin.read()
            proof_tok = "Proof."
            proof_loc = contents.find(proof_tok)
            while proof_loc != -1:
                file_prefix = f"{contents[:(proof_loc + len(proof_tok))]} {SEARCH_TOKEN}"
                all_proof_prefixes.append((physical_path, file_prefix))
                proof_loc = contents.find(proof_tok, proof_loc + 1)

        #random.shuffle(all_proof_prefixes)
        for file, proof_prefix in all_proof_prefixes:
            file_basename = os.path.basename(file)
            file_dirname = os.path.dirname(file)
            hidden_file_path, aux_hidden_file_path = hidden_files_from_prefix(file, proof_prefix)
            yield file, proof_prefix, hidden_file_path, aux_hidden_file_path 


    def save_search_result(self, orig_file_path: str, proof_prefix: str,
                           search_result: SearchResult) -> None:
        orig_file_basename = orig_file_path.lstrip(self.file_tree_loc).lstrip("/").lstrip("\"").lstrip(DESIRED_PREFIX)
        save_path_name = orig_file_basename.replace("/", "-").replace("\\", "-")
        save_name = f"{save_path_name}:{len(proof_prefix)}.json"
        save_loc = os.path.join(self.results_loc, save_name)
        eval_search_result = EvalSearchResult(search_result, orig_file_path, proof_prefix)
        with open(save_loc, "w") as fout:
            fout.write(json.dumps(eval_search_result.to_json(), indent=2))


    def get_search_result(self, orig_file: str, proof_prefix: str, 
                          hidden_file: str, aux_hidden_file: str,
                          lm_example_conf: LmExampleConfig) -> SearchResult:
        print(f"File: {orig_file}")
        start = time.time_ns()
        with ProofFile(hidden_file) as proof_file:
            end = time.time_ns()
            print("Proof file inst:", (end - start) / 1e9)
            with ProofManager(hidden_file, proof_file, 
                                aux_hidden_file, lm_example_conf) as proof_manager:
                initial_check = proof_manager.check_proof("", "", []) 
                if initial_check.tactic_result in (TacticResult.INVALID, TacticResult.COMPLETE):
                    print(f"Skipping {hidden_file} with result {initial_check.tactic_result.name}.")
                    raise ValueError(f"Skipping {hidden_file} with result {initial_check.tactic_result.name}.")
                searcher = SearchTreeManager(self.model_wrapper, 
                                            proof_manager,
                                            self.node_score_type,
                                            self.branching_factor,
                                            self.max_leaf_expansions,
                                            self.timeout)
                search_result = searcher.search()
        return search_result


    def evaluate(self) -> None:
        generator = self.proof_generator()
        num_proof_attempts = 0
        num_correct_proofs = 0
        num_errors = 0
        lm_example_conf = self.model_wrapper.lm_example_config
        for orig_file, proof_prefix, hidden_file, aux_hidden_file in generator:
            if num_proof_attempts >= self.num_proofs:
                break
            try:
                search_result = self.get_search_result(
                    orig_file, proof_prefix, hidden_file, aux_hidden_file, lm_example_conf)
                self.save_search_result(orig_file, proof_prefix, search_result)
                if search_result.found_proof():
                    num_correct_proofs += 1
                num_proof_attempts += 1
            except:
                num_errors += 1
            print(f"Correct Proofs: {num_correct_proofs}")
            print(f"Proof Attempts: {num_proof_attempts}")
            print(f"Num Errors: {num_errors}")


def evaluate(evaluate_conf_loc: str) -> None:

    with open(evaluate_conf_loc, "r") as fin:
        evaluate_conf = load(fin, Loader=Loader)

    assignment_loc = evaluate_conf["assignment_loc"]
    results_loc = evaluate_conf["results_loc"]
    file_tree_loc = evaluate_conf["file_tree_loc"]
    split = evaluate_conf["split"]
    timeout = evaluate_conf["timeout"]
    num_proofs = evaluate_conf["num_proofs"]
    branching_factor = evaluate_conf["branching_factor"]
    max_leaf_expandsions = evaluate_conf["max_leaf_expansions"]

    model_wrapper_alias = evaluate_conf["model_wrapper"]
    model_wrapper_type = MODEL_WRAPPER_ALIASES[model_wrapper_alias]
    model_wrapper = model_wrapper_type.from_json(
        evaluate_conf[model_wrapper_alias])
    node_score_type = NODE_SCORE_ALIASES[evaluate_conf["node_score"]]
    exaple_type = LMEXAMPLE_ALIASES[evaluate_conf["example_type"]]

    if os.path.exists(results_loc):
        print(f"{results_loc} exists.", file=sys.stderr)
        exit(1)
    os.makedirs(results_loc)
    shutil.copy(evaluate_conf_loc, results_loc)

    model_wrapper.get_recs(LmExample("hi", "there"), 2)

    evaluator = Evaluator(
        assignment_loc,
        results_loc,
        file_tree_loc,
        split,
        timeout,
        num_proofs,
        branching_factor,
        max_leaf_expandsions,
        model_wrapper,
        node_score_type,
        exaple_type,
    )

    evaluator.evaluate()


if __name__=="__main__":
    parser = argparse.ArgumentParser(
        description=("Run evaluation on a given model."))
    parser.add_argument("eval_config", help="Path to eval configuration file.")
    args = parser.parse_args(sys.argv[1:])
    evaluate(args.eval_config)

    