
type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

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

(** val prop1 : word list -> bar **)

let prop1 ws =
  Bar2 ((Cons (Nil, ws)), (fun w -> Bar1 ((Cons (w, (Cons (Nil, ws)))),
    (Good0 ((Cons (Nil, ws)), w, (L0 (Nil, ws)))))))

(** val lemma1 : word list -> word -> letter -> l -> l **)

let rec lemma1 _ xs x = function
| L0 (w, ws) -> L0 (w, ws)
| L1 (w, ws, l0) -> L1 (w, ws, (lemma1 ws xs x l0))

(** val lemma2' : word list -> word list -> letter -> word -> r -> l -> l **)

let rec lemma2' _ _ x xs h h0 =
  match h with
  | R0 -> assert false (* absurd case *)
  | R1 (vs, ws, w, r0) ->
    (match h0 with
     | L0 (_, _) -> L0 ((Cons (x, w)), ws)
     | L1 (_, _, x0) -> L1 ((Cons (x, w)), ws, (lemma2' vs ws x xs r0 x0)))

(** val lemma2 : word list -> word list -> letter -> r -> good -> good **)

let rec lemma2 _ _ a h h0 =
  match h with
  | R0 -> h0
  | R1 (vs, ws, w, r0) ->
    (match h0 with
     | Good0 (_, _, x) -> Good0 (ws, (Cons (a, w)), (lemma2' vs ws a w r0 x))
     | Good1 (_, _, x) -> Good1 (ws, (Cons (a, w)), (lemma2 vs ws a r0 x)))

(** val lemma3' : word list -> word list -> letter -> word -> t -> l -> l **)

let rec lemma3' _ _ x xs h h0 =
  match h with
  | T0 (_, w, _, zs, _) ->
    (match h0 with
     | L0 (_, _) -> L0 ((Cons (x, w)), zs)
     | L1 (_, _, x0) ->
       lemma1 (Cons ((Cons (x, w)), zs)) xs x (L1 ((Cons (x, w)), zs, x0)))
  | T1 (w, ws, zs, t0) ->
    (match h0 with
     | L0 (_, _) -> L0 ((Cons (x, w)), zs)
     | L1 (_, _, x0) -> L1 ((Cons (x, w)), zs, (lemma3' ws zs x xs t0 x0)))
  | T2 (b, w, ws, zs, t0) ->
    L1 ((Cons (b, w)), zs, (lemma3' ws zs x xs t0 h0))

(** val lemma3 : word list -> word list -> letter -> t -> good -> good **)

let rec lemma3 _ _ a h h0 =
  match h with
  | T0 (_, w, _, zs, _) ->
    (match h0 with
     | Good0 (_, _, x) -> Good0 (zs, (Cons (a, w)), (lemma1 zs w a x))
     | Good1 (_, _, x) -> Good1 (zs, (Cons (a, w)), x))
  | T1 (w, ws, zs, t0) ->
    (match h0 with
     | Good0 (_, _, x) -> Good0 (zs, (Cons (a, w)), (lemma3' ws zs a w t0 x))
     | Good1 (_, _, x) -> Good1 (zs, (Cons (a, w)), (lemma3 ws zs a t0 x)))
  | T2 (b, w, ws, zs, t0) -> Good1 (zs, (Cons (b, w)), (lemma3 ws zs a t0 h0))

(** val lemma4 : word list -> word list -> letter -> r -> t **)

let rec lemma4 _ _ a = function
| R0 -> assert false (* absurd case *)
| R1 (vs, ws, w, r0) ->
  (match vs with
   | Nil ->
     (match r0 with
      | R0 ->
        (match a with
         | A -> T0 (B, w, Nil, Nil, R0)
         | B -> T0 (A, w, Nil, Nil, R0))
      | R1 (_, _, _, _) -> assert false (* absurd case *))
   | Cons (w0, l0) -> T1 (w, (Cons (w0, l0)), ws, (lemma4 vs ws a r0)))

(** val letter_eq_dec : letter -> letter -> sumbool **)

let letter_eq_dec a b =
  match a with
  | A -> (match b with
          | A -> Left
          | B -> Right)
  | B -> (match b with
          | A -> Right
          | B -> Left)

(** val prop2 :
    letter -> letter -> word list -> bar -> word list -> bar -> word list ->
    t -> t -> bar **)

let rec prop2 a b _ h ys h0 =
  match h with
  | Bar1 (ws, g) ->
    (fun zs h1 _ -> Bar2 (zs, (fun w -> Bar1 ((Cons (w, zs)), (Good1 (zs, w,
      (lemma3 ws zs a h1 g)))))))
  | Bar2 (ws, b0) ->
    let rec f _ b1 zs h2 h3 =
      match b1 with
      | Bar1 (ws0, g) ->
        Bar2 (zs, (fun w -> Bar1 ((Cons (w, zs)), (Good1 (zs, w,
          (lemma3 ws0 zs b h3 g))))))
      | Bar2 (ws0, b2) ->
        Bar2 (zs, (fun w ->
          match w with
          | Nil -> prop1 zs
          | Cons (l0, l1) ->
            (match letter_eq_dec l0 a with
             | Left ->
               prop2 a b (Cons (l1, ws)) (b0 l1) ws0 (Bar2 (ws0, b2)) (Cons
                 ((Cons (a, l1)), zs)) (T1 (l1, ws, zs, h2)) (T2 (a, l1, ws0,
                 zs, h3))
             | Right ->
               f (Cons (l1, ws0)) (b2 l1) (Cons ((Cons (b, l1)), zs)) (T2 (b,
                 l1, ws, zs, h2)) (T1 (l1, ws0, zs, h3)))))
    in f ys h0

(** val prop3 : letter -> word list -> bar -> word list -> r -> bar **)

let rec prop3 a _ h zs x =
  match h with
  | Bar1 (ws, g) ->
    Bar2 (zs, (fun w -> Bar1 ((Cons (w, zs)), (Good1 (zs, w,
      (lemma2 ws zs a x g))))))
  | Bar2 (ws, b) ->
    Bar2 (zs, (fun w ->
      let rec f = function
      | Nil -> prop1 zs
      | Cons (y, l1) ->
        (match letter_eq_dec y a with
         | Left ->
           prop3 a (Cons (l1, ws)) (b l1) (Cons ((Cons (a, l1)), zs)) (R1
             (ws, zs, l1, x))
         | Right ->
           prop2 y a (Cons (l1, zs)) (f l1) ws (Bar2 (ws, b)) (Cons ((Cons
             (y, l1)), zs)) (T0 (a, l1, ws, zs, x)) (T2 (y, l1, ws, zs,
             (lemma4 ws zs a x))))
      in f w))

(** val higman : bar **)

let higman =
  Bar2 (Nil, (fun w ->
    let rec f = function
    | Nil -> prop1 Nil
    | Cons (y, l1) ->
      prop3 y (Cons (l1, Nil)) (f l1) (Cons ((Cons (y, l1)), Nil)) (R1 (Nil,
        Nil, l1, R0))
    in f w))

(** val l_idx : (nat -> word) -> word -> word list -> l -> nat **)

let rec l_idx f w _ = function
| L0 (_, ws) -> length ws
| L1 (_, ws, l0) -> l_idx f w ws l0

(** val good_idx : (nat -> word) -> word list -> good -> (nat, nat) sigT **)

let rec good_idx f _ = function
| Good0 (ws, w, l0) -> ExistT ((l_idx f w ws l0), (length ws))
| Good1 (ws, _, g) -> good_idx f ws g

(** val bar_idx : (nat -> word) -> word list -> bar -> (nat, nat) sigT **)

let rec bar_idx f _ = function
| Bar1 (ws, g) -> good_idx f ws g
| Bar2 (ws, b) -> let w = f (length ws) in bar_idx f (Cons (w, ws)) (b w)

(** val higman_idx : (nat -> word) -> (nat, nat) sigT **)

let higman_idx f =
  bar_idx f Nil higman
