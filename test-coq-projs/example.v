Require Import Coq.Unicode.Utf8.

Ltac reduce_eq := simpl; reflexivity.

Theorem mult_0_plus : ∀ n m : nat, 0 + (S n * m) = S n * m.
Proof.
    intros n m.
Admitted.