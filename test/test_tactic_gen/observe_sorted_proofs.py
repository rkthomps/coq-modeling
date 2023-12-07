from tactic_gen.proof_distance import SortedProofs, StrippedProof


proof1 = """
Proof.
    intros n. induction n as [|n' IHn'].
    - reflexivity. 
    - simpl. rewrite IHn'. reflexivity. 
Qed.
"""

proof2 = """
Proof.
  intros. induction l as [| h l' IHl'].
  - reflexivity. 
  - simpl. destruct (n <=? h) eqn:E.
    + rewrite ord_rewrite. rewrite E. apply H.  
    + destruct (ins n l') as [|insH insTL] eqn:E1. 
      * reflexivity.
      * rewrite ord_rewrite. apply andb_true_iff. split.
        -- destruct l' as [|h' l''] eqn:E2. 
          ++ simpl in E1. injection E1 as E1A E1B. 
             rewrite <- E1A. apply leb_flip. apply E.
          ++ simpl in E1. destruct (n <=? h') eqn:E3. 
             ** injection E1 as E1A E1B. rewrite <- E1A. 
                apply leb_flip. apply E. 
             ** injection E1 as E1A E1B. rewrite <- E1A.
                rewrite ord_rewrite in H. 
                apply andb_true_iff in H. destruct H as [H1 H2].
                apply H1. 
        -- apply IHl'. apply tl_ordered in H. apply H. 
Qed.
"""

proof3 = """
Proof.
  intros. generalize dependent n2. induction n1 as [|n1' IHn1']; intros.  
  - reflexivity. 
  - simpl. destruct n2 as [|n2'].
    + discriminate H. 
    + apply IHn1'. apply ltb_through_succ. apply H. 
Qed.
"""

target = StrippedProof.from_text(proof3)

print("Loading proof bank...")
proof_bank = SortedProofs.load("/home/ubuntu/coq-modeling/distances/test.json")

print("Finding top 10...")
top_n = proof_bank.nearest_n(target, 10)

for sc in top_n:
    print("-" * 10)
    print("Score", sc.score)
    print(sc.proof.to_string())
