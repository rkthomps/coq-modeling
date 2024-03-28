Require Import Nat.


Lemma succ_preserves_eq: forall (n1 n2 : nat),
    (n1 <=? n2 = true) <-> ((S n1) <=? (S n2) = true).
Proof. 
induction n1; intuition; simpl in *.
destruct n2; intuition. 
Qed.

Lemma if_ltb_then_leb: forall (n1 n2 : nat),
    (n1 <? n2 = true) -> (n1 <=? n2 = true). 
Proof.
  intros n1 n2.
  destruct (n1 <? n2).
  - intros H.
    destruct (n1 <=? n2).
Admitted.

  (* unfold ltb. intros n1. induction n1 as [|n1' IHn1']. 
  - reflexivity.  
  - intros n2. destruct n2 as [|n2'] eqn:E. 
    + intros H. discriminate H.  
    + intros. apply -> succ_preserves_eq. apply <- succ_preserves_eq in H. 
      apply IHn1'. apply H. 
Qed. *)


(* Lemma if_ltb_then_leb: forall (n1 n2 : nat),
    (n1 <? n2 = true) -> (n1 <=? n2 = true).
Proof.
<prove> *)
