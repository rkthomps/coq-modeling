Require Import Nat.

Lemma leb_refl: forall (n : nat), (n <=? n) = true.
Proof.
intros. induction n as [|n' IHn']. 
- reflexivity. 
- simpl. apply IHn'. 
Qed. 