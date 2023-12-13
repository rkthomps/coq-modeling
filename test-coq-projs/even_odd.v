

Definition odd (n : nat) := exists k, n = 2 * k + 1.
Definition even (n: nat) := exists k, n = 2 * k.

Lemma sum_odds: forall (n1 n2 : nat),
  odd n1 -> odd n2 -> even (n1 + n2).
intros.
destruct H.
destruct H0.
rewrite H, H0.
exists (2 * x + 1 + (2 * x0 + 1)).
simpl.
rewrite <- plus_n_O.
rewrite <- plus_n_O.
rewrite <- plus_n_O.
rewrite <- plus_n_Sm.
rewrite <- plus_n_O.
rewrite <- plus_n_Sm.
rewrite <- plus_n_O.
rewrite <- plus_n_Sm.
rewrite <- plus_n_Sm.
rewrite plus_n_Sm.
rewrite plus_n_Sm.
simpl.
rewrite <- plus_n_Sm.
rewrite <- plus_n_Sm.
rewrite plus_n_Sm.
rewrite plus_n_Sm.
rewrite plus_n_Sm.
rewrite plus_n_Sm.
rewrite plus_n_Sm.
rewrite plus_n_Sm.
rewrite <- plus_n_Sm.
rewrite <- plus_n_Sm.
rewrite <- plus_n_Sm.
simpl.
rewrite <- plus_n_Sm.
rewrite <- plus_n_Sm.
simpl.
rewrite plus_n_Sm.
rewrite plus_n_Sm.
rewrite plus_n_Sm.
rewrite plus_n_Sm.
rewrite plus_n_Sm.
rewrite <- plus_n_Sm.
rewrite <- plus_n_Sm.
rewrite <- plus_n_Sm.
rewrite <- plus_n_Sm.
rewrite plus_n_Sm.
rewrite <- plus_n_Sm.
rewrite <- plus_n_Sm.
rewrite plus_n_Sm.
rewrite plus_n_Sm.
rewrite plus_n_Sm.
rewrite <- plus_n_Sm.
rewrite plus_n_Sm.
Admitted.