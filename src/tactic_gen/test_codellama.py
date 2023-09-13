
from typing import Any 
import sys, os
import requests
import json

import jsonlines

from coqlspclient.coq_file import CoqFile
from coqlspclient.proof_state import ProofState, ProofTerm, ProofStep
from coqlspclient.coq_structs import Term

from data_management.dataset_file import STEPS_NAME, FILE_CONTEXT_NAME, DatasetFile
from data_management.lm_example import LmExample, BasicLmExample



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


def get_last_step_data_point(proof: ProofTerm) -> Any:
    step = proof.steps[-1]
    goals = list(map(lambda goal: repr(goal), step.goals.goals.goals))
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
        "n_step": len(proof.steps),
        "goals": goals,
        "next_steps": []
    }
    return data_point 

def update_search_dir(search_dir: str, 
                      last_proof: ProofTerm, 
                      proof_step_data: Any, 
                      context_data: Any) -> None:
    steps_loc = os.path.join(search_dir, STEPS_NAME)
    context_loc = os.path.join(search_dir, FILE_CONTEXT_NAME)
    if not os.path.exists(search_dir):
        os.makedirs(search_dir)
    if os.path.exists(steps_loc):
        os.remove(steps_loc)
    if os.path.exists(context_loc):
        os.remove(context_loc)

    with jsonlines.open(steps_loc, "w") as fout:
        fout.write_all([proof_step_data])
    with jsonlines.open(context_loc, "w") as fout:
        fout.write_all([{
            "file": proc_file_path(last_proof.file_path),
            "context": context_data}])
    

SEARCH_DIR = ".proof-search"
EXAMPLE_LOC = "/home/ubuntu/coq-modeling/test-coq-projs/example.v"
TIMEOUT = 60

SERVER_URL = "http://127.0.0.1:5000/codellama"

# Assume the proof is "stuck on the last step of the last proof."
with CoqFile(EXAMPLE_LOC, timeout=TIMEOUT) as coq_file:
    with ProofState(coq_file) as proof_state:
        print("Getting info")
        proofs = proof_state.proofs
        context = proof_state.context
        context_data = get_context(list(context.terms.values()))
        assert len(proofs) > 0
        last_proof = proofs[-1] 
        assert len(last_proof.steps) > 0
        last_step = last_proof.steps[-1]
        assert "Admitted" in last_step.text
        proof_step_data = get_last_step_data_point(last_proof)
        update_search_dir(SEARCH_DIR, last_proof, proof_step_data, context_data)
        dataset_obj = DatasetFile.from_directory(SEARCH_DIR)
        examples = BasicLmExample.from_dataset_file(dataset_obj)
        assert len(examples) == 1
        example = examples[0]
        print("input:", example.input)
        print("output:", example.output)
        request_data = example.to_json()
        model_response = requests.post(SERVER_URL, request_data)
        response_dic = json.loads(model_response.content)
        print(response_dic["output"])




