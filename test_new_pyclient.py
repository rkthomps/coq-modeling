



from coqlspclient.coq_file import CoqFile
from coqlspclient.coq_structs import ProofTerm
from coqlspclient.proof_file import ProofFile
import time


#PATH = "/home/ubuntu/coq-modeling/test-coq-projs/min.v"
PATH = "/home/ubuntu/coq-modeling/test-coq-projs/lt_impl.v"

# with CoqFile(PATH, timeout=60) as coq_file:
#     coq_file.exec(nsteps=6)
#     print("Valid?:", coq_file.is_valid)
#     print("Number of terms:", len(coq_file.context.terms))
#     print("Goals:", coq_file.current_goals())

def print_proofs(proofs: list[ProofTerm]) -> None:
    for proof in proofs:
        print(proof.text, end="")
        for step in proof.steps:
            print(step.text, end="")
        print("\n")

def add_step_to_proof_term(proof_file: ProofFile, proof: ProofTerm, step: str) -> None: 
    proof_file.add_step(step, proof.steps[-1].ast.range)

with ProofFile(PATH, timeout=30) as proof_file:
    print_proofs(proof_file.proofs)
    prev_idx = len(proof_file.steps) - 3
    print("Prev step:", proof_file.steps[prev_idx].text)
    print(repr(proof_file.proofs[-1].steps[-1].goals.goals.goals))
    proof_file.add_step(" apply H.", prev_idx)
    print(repr(proof_file.proofs[-1].steps[-1].goals.goals.goals))
    print_proofs(proof_file.proofs)
    
