

import sys, os
import argparse
import json
import re

from evaluation.evaluate import EvalSearchResult


def load_eval_result(eval_file: str) -> EvalSearchResult:
    with open(eval_file, "r") as fin:
        eval_data = json.load(fin)
    return EvalSearchResult.from_json(eval_data)


eval_filename_pattern = re.compile(r"(.*?)(\d+).json")




# def compare_evals_file_specific(eval_dirs: list[str], file: str) -> None:

#     valid_
#     for eval_dir in eval_dirs:
#         for eval_file in os.listdir(eval_dir):
#             filename_match = eval_filename_pattern.match(eval_file)
#             if filename_match is None:
#                 continue
#             file_name, num_char_str = filename_match.groups()
#             if filename


def compare_evals_one_correct(eval_dirs: list[str]) -> None:
    assert len(eval_dirs) > 0
    proof_sets: list[set[str]] = []
    qed_set: set[str] = set()
    for eval_dir in eval_dirs:
        proof_set: set[str] = set()
        for eval_file in os.listdir(eval_dir):
            if not eval_file.endswith(".json"):
                continue
            eval_file_loc = os.path.join(eval_dir, eval_file)
            proof_set.add(eval_file)
            eval_result = load_eval_result(eval_file_loc)
            if eval_result.search_result.found_proof():
                qed_set.add(eval_file)
        proof_sets.append(proof_set)
    assert len(proof_sets) == len(eval_dirs)

    print("Proof set:", proof_set)
    print("Qed set", qed_set)
    
    cross_eval_proofs = proof_sets[0]
    for proof_set in proof_sets[1:]:
        cross_eval_proofs = cross_eval_proofs & proof_set
    
    at_least_one_qed_proofs = cross_eval_proofs & qed_set

    for proof_file_name in at_least_one_qed_proofs:
        proof_prefixes: list[str] = []
        eval_names: list[str] = []
        correct_incorrect: list[str] = []
        proof_attempts: list[str] = []
        for eval_dir in eval_dirs:
            eval_loc = os.path.join(eval_dir, proof_file_name)
            if not os.path.exists(eval_loc):
                continue
            eval_result = load_eval_result(eval_loc) 
            proof_prefixes.append(eval_result.proof_prefix)
            eval_names.append(eval_dir)
            if eval_result.search_result.found_proof():
                correct_incorrect.append("Correct")
                assert eval_result.search_result.qed_node is not None
                proof_attempts.append(eval_result.search_result.qed_node.combined_model_tactics)
            else:
                correct_incorrect.append("Incorrect")
                deepest_node, _ = eval_result.search_result.search_tree.get_deepest_node()
                proof_attempts.append(deepest_node.combined_model_tactics)

        assert len(proof_prefixes) == len(eval_names) == len(correct_incorrect) == len(proof_attempts)
        assert len(proof_prefixes) > 0
        print(f"=================== Proof File: {proof_file_name} =================")
        print(proof_prefixes[0])
        for eval_name, result_str, attempt in zip(eval_names, correct_incorrect, proof_attempts):
            print(f"------------{eval_name} {result_str} Attempt:----------------")
            print(attempt)




if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Compare multiple evaluations.")
    parser.add_argument("eval_dirs", nargs="+", type=str)
    args = parser.parse_args(sys.argv[1:])
    compare_evals(args.eval_dirs)

