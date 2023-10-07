
Require Import Coq.Lists.List.
Require Import Nat.

(* Definition t := (forall l : list nat,
l <> nil ->
exists h : nat, min l = Some h). *)

Definition def_one := (forall bananaberry : list nat,
bananaberry <> nil ->
exists ks : nat, min bananaberry = Some ks).