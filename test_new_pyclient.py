



from coqlspclient.coq_file import CoqFile
from coqlspclient.coq_structs import ProofTerm
from coqlspclient.proof_file import ProofFile
import time


PATH = "/home/ubuntu/coq-modeling/test-coq-projs/min.v"
#PATH = "/home/ubuntu/coq-modeling/test-coq-projs/___min.v"
#PATH = "/home/ubuntu/coq-modeling/test-coq-projs/aux_lt_impl.v"
#PATH = "/home/ubuntu/coq-modeling/test-coq-projs/lt_trans.v"

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


# start = time.time_ns()
# with CoqFile(PATH) as coq_file:
#     coq_file.run()
#     print(coq_file.is_valid)
#     print(coq_file.in_proof)
# end = time.time_ns()
# print((end - start) / (1e9))

with ProofFile(PATH) as proof_file:
    proof_file.add_step("\nintros. ", len(proof_file.steps) - 2)


    #proof_file.add_step(" destruct (a <? n).", len(proof_file.steps) - 3)

# with ProofFile(PATH, timeout=30) as proof_file:
#     print_proofs(proof_file.proofs)

    # prev_idx = len(proof_file.steps) - 3
    # print("Prev step:", proof_file.steps[prev_idx].text)
    # print(repr(proof_file.proofs[-1].steps[-1].goals.goals.goals))
    # proof_file.add_step(" apply H.", prev_idx)
    # print(repr(proof_file.proofs[-1].steps[-1].goals.goals.goals))
    # print_proofs(proof_file.proofs)
    