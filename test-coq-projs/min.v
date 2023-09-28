Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

Fixpoint min (l : (list nat)) : option nat := 
    match l with
    | nil => None
    | h :: tl => match (min tl) with
        | None => Some h 
        | Some m => if (h <? m) then (Some h) else (Some m)
        end
    end.

Lemma exists_min: forall (l : (list nat)), 
    (l <> nil) -> exists h, min(l) = Some(h).
Proof. 
  intros l H.
   destruct l.
   - contradiction.
   - simpl. destruct (min l) eqn:E.
<prove>
 
(* Lemma exists_min: forall (l : (list nat)), 
    (l <> nil) -> exists h, min(l) = Some(h).
Proof.
  intros l H.
   destruct l.
   - contradiction.
   - simpl. destruct (min l) eqn:E.
     + destruct (n <? n0) eqn:E1.
       * exists n. reflexivity.
       * exists n0. reflexivity.
     + exists n. reflexivity.
Qed. *)

Definition myprop (n1 n2 : nat): bool := n1 + n2 =? n1 * n2. 
