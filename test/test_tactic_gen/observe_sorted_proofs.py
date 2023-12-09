from tactic_gen.proof_distance import SortedProofs, StrippedProof


proof1 = """
Proof.
    intros n. induction n as [|n' IHn'].
    - reflexivity. 
    - simpl. rewrite IHn'. reflexivity. 
Qed.
"""

thm1 = """
Lemma add_zero_r: forall (n : nat),
    n + 0 = n. 
Proof."""

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

thm4 = """
Lemma exists_min: forall (l : (list nat)), 
    (l <> nil) -> exists h, min(l) = Some(h).
"""
proof4 = """
Proof.
    intros l H. destruct l.
    - contradiction.
    - simpl. destruct (min l).
      + destruct (n <? n0).
        * exists n. reflexivity.
        * exists n0. reflexivity.
      + exists n. reflexivity.
Qed.
"""

thm5 = """
Theorem min_superlist_less: forall (l : (list nat)) (n1 n2 x1 x2: nat),
    min (n2 :: l) = Some x1 -> 
    min (n1 :: n2 :: l) = Some x2 ->
    x2 <=? x1 = true. 
"""

proof5 = """
Proof. 
    intros. rewrite min_rewrite in H0. rewrite H in H0.  
    destruct (n1 <? x1) eqn:E.
    - injection H0 as H0. rewrite H0 in E. apply if_ltb_then_leb.  
      apply E. 
    - injection H0 as H0. rewrite H0. apply leb_refl. 
Qed. 
"""

target = StrippedProof.from_text(proof5)

print("Loading proof bank...")
proof_bank = SortedProofs.load(
    "/home/ubuntu/coq-modeling/distances/random-split-distances.json"
)

print("Finding top 10...")
top_n = proof_bank.nearest_n(target, 30)

for sc in top_n:
    print("-" * 10)
    print("Score", sc.score)
    print(sc.proof.to_string())
