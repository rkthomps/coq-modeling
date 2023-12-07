from tactic_gen.proof_distance import SortedProofs, StrippedProof

my_proof = """
Proof.
    intros n. induction n as [|n' IHn'].
    - reflexivity. 
    - simpl. rewrite IHn'. reflexivity. 
Qed.
"""

target = StrippedProof.from_text(my_proof)

proof_bank = SortedProofs.load("/home/kthompson/coq-modeling/distances/test.json")

top_n = proof_bank.nearest_n(target, 10)

for sc in top_n:
    print("-" * 10)
    print("Score", sc.score)
    print(sc.proof.to_string())
