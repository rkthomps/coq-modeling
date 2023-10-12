Require Import Nat.

Lemma leq_trans: forall (n1 n2 n3 : nat), 
    (n1 <=? n2 = true) -> 
    (n2 <=? n3 = true) -> 
    (n1 <=? n3 = true). 
Proof.
<prove>

(* Lemma leq_trans: forall (n1 n2 n3 : nat), 
    (n1 <=? n2 = true) -> 
    (n2 <=? n3 = true) -> 
    (n1 <=? n3 = true). 
Proof.
    intros n1. induction n1 as [|n1' IHn1'].
    - intros. reflexivity.  
    - intros. destruct n2 as [|n2']. 
      + discriminate H. 
      + destruct n3 as [|n3'].
        * discriminate H0. 
        * simpl. apply IHn1' with(n2:=n2'). 
          -- simpl in H. apply H. 
          -- simpl in H0. apply H0. 
      Qed.  *)