Require Import Nat.

Lemma if_ltb_then_leb: forall (n1 n2 : nat),
    (n1 <? n2 = true) -> (n1 <=? n2 = true).
Proof.
<prove>