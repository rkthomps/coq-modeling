Require Import Nat.

Lemma leb_refl: forall (n : nat), (n <=? n) = true.
Proof.
intros n. induction n as [|n' IHn'].
- reflexivity.
- <prove> 