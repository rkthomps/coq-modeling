Require Import Nat.


Lemma if_ltb_then_leb: forall (n1 n2 : nat),
    (n1 <? n2 = true) -> (n1 <=? n2 = true). 
Proof.
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
