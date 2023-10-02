
from typing import Any, Iterable
import json
import sys, os
import argparse
import random
import traceback


from coqlspclient.coq_file import CoqFile
from coqlspclient.coq_lsp_structs import Position

from tactic_gen.lm_example import LmExample, LMEXAMPLE_ALIASES
from data_management.split_raw_data import SPLITS, assignment_shape_expected
from model_deployment.searcher import ProofManager, SearchTreeManager, get_fresh_path, TacticResult, ProofSearchTree
from model_deployment.model_wrapper import ModelWrapper, MODEL_WRAPPER_ALIASES 
from model_deployment.node_score import NodeScore, NODE_SCORE_ALIASES
from evaluation.impose_file_hierarchy import mapping_shape_correct, FILE_MAPPING_NAME

from tqdm import tqdm
from yaml import load, Loader 


# Need a proof
class Evaluator:
    def __init__(self, 
                 assignment_loc: str, 
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
        assert type(split) == str
        assert type(timeout) == int
        assert type(num_proofs) == int
        assert type(max_leaf_expansions) ==int
        assert type(branching_factor) == int
        assert isinstance(model_wrapper, ModelWrapper)
        assert type(node_score_type) == type 
        assert type(example_type) == type
        self.assignments_loc = assignment_loc
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


    def proof_generator(self) -> Iterable[str]:
        with open(self.assignments_loc, "r") as fin:
            assignment = json.load(fin)
        assert assignment_shape_expected(assignment)
        mapping_loc = os.path.join(self.file_tree_loc, FILE_MAPPING_NAME)
        with open(mapping_loc, "r") as fin:
            mapping = json.load(fin) 
        assert mapping_shape_correct(mapping)
        assert self.split in SPLITS
        eligible_files = assignment[self.split]
        all_proof_prefixes: list[tuple[str, str]] = []
        print("Indexing Proofs...")
        for file in tqdm(eligible_files):
            physical_path = mapping[file]
            with open(physical_path, "r") as fin:
                contents = fin.read()
            proof_tok = "Proof."
            proof_loc = contents.find(proof_tok)
            while proof_loc != -1:
                file_prefix = f"{contents[:(proof_loc + len(proof_tok))]} {ProofManager.SEARCH_TOKEN}"
                all_proof_prefixes.append((physical_path, file_prefix))
                proof_loc = contents.find(proof_tok, proof_loc + 1)

        random.shuffle(all_proof_prefixes)
        for file, proof_prefix in all_proof_prefixes:
            file_basename = os.path.basename(file)
            file_dirname = os.path.dirname(file)
            fresh_file = get_fresh_path(file_dirname, file_basename) 
            with open(fresh_file, "w") as fout:
                fout.write(proof_prefix)
            yield fresh_file


    def find_proof_positions(self, filename: str) -> list[Position]:
        parent_dir = os.path.dirname(filename)
        os.chdir(parent_dir)
        proof_positions = []
        with CoqFile(filename, timeout=60) as coq_file:
            cur_in_proof = False
            while not coq_file.checked:
                coq_file.exec()
                if coq_file.in_proof and not cur_in_proof: 
                    cur_in_proof = True
                    pos = coq_file.ast[coq_file.steps_taken].range.start
                    proof_positions.append(pos)
                if cur_in_proof and not coq_file.in_proof:
                    cur_in_proof = False
        return proof_positions


    def evaluate(self) -> None:
        generator = self.proof_generator()
        num_proof_attempts = 0
        num_correct_proofs = 0
        proof_trees: list[ProofSearchTree] = []
        for psuedo_file in generator:
            if num_proof_attempts >= self.num_proofs:
                break
            try:
                proof_manager = ProofManager(psuedo_file, self.example_type)
            except Exception as e:
                traceback.print_exc()
                continue
            empty_result, goal_answer = proof_manager.check_proof("") 
            if empty_result == TacticResult.INVALID:
                continue
            if empty_result == TacticResult.COMPLETE:
                continue
            searcher = SearchTreeManager(self.model_wrapper, 
                                         proof_manager,
                                         self.node_score_type,
                                         self.branching_factor,
                                         self.max_leaf_expansions,
                                         self.timeout)
            search_result = searcher.search()
            proof_trees.append(search_result.search_tree)
            if search_result.found_proof():
                num_correct_proofs += 1
            num_proof_attempts += 1
            print(f"\n\n{num_correct_proofs} correct out of {num_proof_attempts}.\n\n")


def evaluate(evaluate_conf: dict[str, Any]) -> None:
    assignment_loc = evaluate_conf["assignment_loc"]
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

    evaluator = Evaluator(
        assignment_loc,
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
    with open(args.eval_config, "r") as fin:
        conf = load(fin, Loader=Loader)
    evaluate(conf)

    