Require Import Nat.

Lemma leb_refl: forall (n : nat), (n <=? n) = true.
Proof.
    intros n. induction n. 
    - reflexivity. 
    - simpl. apply IHn. 
Qed.