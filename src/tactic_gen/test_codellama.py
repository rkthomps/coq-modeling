
from typing import Any 

from coqlspclient.coq_file import CoqFile
from coqlspclient.proof_state import ProofState, ProofTerm, ProofStep
from coqlspclient.coq_structs import Term

EXAMPLE_LOC = "/home/ubuntu/coq-modeling/test-coq-projs/example.v"

def proc_file_path(file_path: str) -> str:
    if file_path.startswith("/home"):
        return "/".join(file_path.split("/")[3:])
    return file_path

def get_context(context: list[Term]) -> list[dict[str, str]]:
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


# Assume the proof is "stuck on the last step of the last proof."
with CoqFile(EXAMPLE_LOC) as coq_file:
    with ProofState(coq_file) as proof_state:
        print("Getting info")
        proofs = proof_state.proofs
        context = proof_state.context
        assert len(proofs) > 0
        last_proof = proofs[-1] 
        assert len(last_proof.steps > 0)
        last_step = last_proof.steps[-1]
        assert "Admitted" in last_step.text
        proof_step_data = get_last_step_data_point(last_proof)

