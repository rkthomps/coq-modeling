
type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

val length : 'a1 list -> nat

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

type sumbool =
| Left
| Right

type letter =
| A
| B

type word = letter list

type l =
| L0 of word * word list
| L1 of word * word list * l

type good =
| Good0 of word list * word * l
| Good1 of word list * word * good

type r =
| R0
| R1 of word list * word list * word * r

type t =
| T0 of letter * word * word list * word list * r
| T1 of word * word list * word list * t
| T2 of letter * word * word list * word list * t

type bar =
| Bar1 of word list * good
| Bar2 of word list * (word -> bar)

val prop1 : word list -> bar

val lemma1 : word list -> word -> letter -> l -> l

val lemma2' : word list -> word list -> letter -> word -> r -> l -> l

val lemma2 : word list -> word list -> letter -> r -> good -> good

val lemma3' : word list -> word list -> letter -> word -> t -> l -> l

val lemma3 : word list -> word list -> letter -> t -> good -> good

val lemma4 : word list -> word list -> letter -> r -> t

val letter_eq_dec : letter -> letter -> sumbool

val prop2 :
  letter -> letter -> word list -> bar -> word list -> bar -> word list -> t
  -> t -> bar

val prop3 : letter -> word list -> bar -> word list -> r -> bar

val higman : bar

val l_idx : (nat -> word) -> word -> word list -> l -> nat

val good_idx : (nat -> word) -> word list -> good -> (nat, nat) sigT

val bar_idx : (nat -> word) -> word list -> bar -> (nat, nat) sigT

val higman_idx : (nat -> word) -> (nat, nat) sigT
