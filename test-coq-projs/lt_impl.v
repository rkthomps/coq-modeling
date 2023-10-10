Require Import Nat.


Lemma succ_preserves_eq: forall (n1 n2 : nat),
    (n1 <=? n2 = true) <-> ((S n1) <=? (S n2) = true).
Proof. 
    split. 
    - generalize dependent n2. induction n1 as [|n1' IHn1']. 
      + reflexivity. 
      + intros. simpl. destruct n2 as [|n2'] eqn:E.  
        * discriminate H. 
        * simpl in H. apply H. 
    - generalize dependent n2. induction n1 as [|n1' IHn1'].
      + reflexivity. 
      + intros. simpl. destruct n2 as [|n2'] eqn:E. 
        * discriminate H. 
        * apply IHn1'. apply IHn1' in H. simpl. apply H.  
Qed.

Lemma if_ltb_then_leb: forall (n1 n2 : nat),
    (n1 <? n2 = true) -> (n1 <=? n2 = true). 
  Proof.
  <prove>

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
