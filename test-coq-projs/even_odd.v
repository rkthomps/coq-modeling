

Definition odd (n : nat) := exists k, n = 2 * k + 1.
Definition even (n: nat) := exists k, n = 2 * k.

Lemma sum_odds: forall (n1 n2 : nat),
  odd n1 -> odd n2 -> even (n1 + n2).
Proof.
Admitted.