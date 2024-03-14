{
  "file_context": [
    "{\"file\": \"repos/yalhessi-verified-verifier/BinaryLattice.v\", \"workspace\": \"repos/yalhessi-verified-verifier\", \"repository\": \"repos/yalhessi-verified-verifier\"}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"'if' c 'is' p 'then' u 'else' v\\\" := (match c with p => u | _ => v end) (at level 200, p pattern at level 100).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Notations.v\", \"module\": [\"IfNotations\"], \"line\": 110}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"A -> B\\\" := (forall (_ : A), B) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 15}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"Inductive True : Prop := I : True.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 21}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"Inductive False : Prop :=.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 28}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition not (A:Prop) := A -> False.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 33}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"~ x\\\" := (not x) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 35}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition notT (A:Type) := A -> False.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 41}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"Inductive and (A B:Prop) : Prop := conj : A -> B -> A /\\\\ B where \\\"A /\\\\ B\\\" := (and A B) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 62}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Inductive and (A B:Prop) : Prop := conj : A -> B -> A /\\\\ B where \\\"A /\\\\ B\\\" := (and A B) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 62}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem proj1 : A /\\\\ B -> A.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 74}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem proj2 : A /\\\\ B -> B.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 79}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"Inductive or (A B:Prop) : Prop := | or_introl : A -> A \\\\/ B | or_intror : B -> A \\\\/ B where \\\"A \\\\/ B\\\" := (or A B) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 88}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Inductive or (A B:Prop) : Prop := | or_introl : A -> A \\\\/ B | or_intror : B -> A \\\\/ B where \\\"A \\\\/ B\\\" := (or A B) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 88}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition iff (A B:Prop) := (A -> B) /\\\\ (B -> A).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 101}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"A <-> B\\\" := (iff A B) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 103}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem iff_refl : forall A:Prop, A <-> A.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 111}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem iff_trans : forall A B C:Prop, (A <-> B) -> (B <-> C) -> (A <-> C).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 116}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem iff_sym : forall A B:Prop, (A <-> B) -> (B <-> A).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 121}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem and_iff_compat_l : forall A B C : Prop, (B <-> C) -> (A /\\\\ B <-> A /\\\\ C).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 133}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem and_iff_compat_r : forall A B C : Prop, (B <-> C) -> (B /\\\\ A <-> C /\\\\ A).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 140}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem or_iff_compat_l : forall A B C : Prop, (B <-> C) -> (A \\\\/ B <-> A \\\\/ C).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 147}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem or_iff_compat_r : forall A B C : Prop, (B <-> C) -> (B \\\\/ A <-> C \\\\/ A).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 154}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem imp_iff_compat_l : forall A B C : Prop, (B <-> C) -> ((A -> B) <-> (A -> C)).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 161}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem imp_iff_compat_r : forall A B C : Prop, (B <-> C) -> ((B -> A) <-> (C -> A)).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 167}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem not_iff_compat : forall A B : Prop, (A <-> B) -> (~ A <-> ~B).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 173}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem neg_false : forall A : Prop, ~ A <-> (A <-> False).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 182}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem and_cancel_l : forall A B C : Prop, (B -> A) -> (C -> A) -> ((A /\\\\ B <-> A /\\\\ C) <-> (B <-> C)).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 189}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem and_cancel_r : forall A B C : Prop, (B -> A) -> (C -> A) -> ((B /\\\\ A <-> C /\\\\ A) <-> (B <-> C)).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 198}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem and_comm : forall A B : Prop, A /\\\\ B <-> B /\\\\ A.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 207}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem and_assoc : forall A B C : Prop, (A /\\\\ B) /\\\\ C <-> A /\\\\ B /\\\\ C.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 212}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem or_cancel_l : forall A B C : Prop, (B -> ~ A) -> (C -> ~ A) -> ((A \\\\/ B <-> A \\\\/ C) <-> (B <-> C)).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 217}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem or_cancel_r : forall A B C : Prop, (B -> ~ A) -> (C -> ~ A) -> ((B \\\\/ A <-> C \\\\/ A) <-> (B <-> C)).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 225}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem or_comm : forall A B : Prop, (A \\\\/ B) <-> (B \\\\/ A).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 233}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem or_assoc : forall A B C : Prop, (A \\\\/ B) \\\\/ C <-> A \\\\/ B \\\\/ C.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 238}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma iff_and : forall A B : Prop, (A <-> B) -> (A -> B) /\\\\ (B -> A).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 248}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma iff_to_and : forall A B : Prop, (A <-> B) <-> (A -> B) /\\\\ (B -> A).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 253}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"Inductive ex (A:Type) (P:A -> Prop) : Prop := ex_intro : forall x:A, P x -> ex (A:=A) P.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 273}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition ex_proj1 (x:ex P) : A := match x with ex_intro _ a _ => a end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 283}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition ex_proj2 (x:ex P) : P (ex_proj1 x) := match x with ex_intro _ _ b => b end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 286}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"Inductive ex2 (A:Type) (P Q:A -> Prop) : Prop := ex_intro2 : forall x:A, P x -> Q x -> ex2 (A:=A) P Q.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 294}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition ex_of_ex2 (A : Prop) (P Q : A -> Prop) (X : ex2 P Q) : ex P := ex_intro P (let (a, _, _) := X in a) (let (x, p, _) as s return (P (let (a, _, _) := s in a)) := X in p).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 309}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition ex_proj3 (x:ex2 P Q) : Q (ex_proj1 (ex_of_ex2 x)) := match x with ex_intro2 _ _ _ _ b => b end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 318}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition all (A:Type) (P:A -> Prop) := forall x:A, P x.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 323}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"'exists' x .. y , p\\\" := (ex (fun x => .. (ex (fun y => p)) ..)) (at level 200, x binder, right associativity, format \\\"'[' 'exists' '/ ' x .. y , '/ ' p ']'\\\") : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 327}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"'exists2' x , p & q\\\" := (ex2 (fun x => p) (fun x => q)) (at level 200, x name, p at level 200, right associativity) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 332}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"'exists2' x : A , p & q\\\" := (ex2 (A:=A) (fun x => p) (fun x => q)) (at level 200, x name, A at level 200, p at level 200, right associativity, format \\\"'[' 'exists2' '/ ' x : A , '/ ' '[' p & '/' q ']' ']'\\\") : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 334}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"'exists2' ' x , p & q\\\" := (ex2 (fun x => p) (fun x => q)) (at level 200, x strict pattern, p at level 200, right associativity) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 339}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"'exists2' ' x : A , p & q\\\" := (ex2 (A:=A) (fun x => p) (fun x => q)) (at level 200, x strict pattern, A at level 200, p at level 200, right associativity, format \\\"'[' 'exists2' '/ ' ' x : A , '/ ' '[' p & '/' q ']' ']'\\\") : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 341}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem inst : forall x:A, all (fun x => P x) -> P x.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 353}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem gen : forall (B:Prop) (f:forall y:A, B -> P y), B -> all P.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 358}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"#[deprecated(since=\\\"8.16\\\",note=\\\"Use eq instead\\\")] Notation identity := eq (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 431}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"Inductive eq (A:Type) (x:A) : A -> Prop := eq_refl : x = x :>A where \\\"x = y :> A\\\" := (@eq A x y) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 376}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"#[deprecated(since=\\\"8.16\\\",note=\\\"Use eq_refl instead\\\")] Notation refl_id := eq_refl (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 463}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Inductive eq (A:Type) (x:A) : A -> Prop := eq_refl : x = x :>A where \\\"x = y :> A\\\" := (@eq A x y) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 376}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"x = y\\\" := (eq x y) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 388}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"x <> y :> T\\\" := (~ x = y :>T) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 389}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"x <> y\\\" := (~ (x = y)) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 390}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem absurd : forall A C:Prop, A -> ~ A -> C.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 406}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"#[deprecated(since=\\\"8.16\\\",note=\\\"Use eq_sym instead\\\")] Notation sym_id := eq_sym (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 465}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem eq_sym : x = y -> y = x.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 417}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"#[deprecated(since=\\\"8.16\\\",note=\\\"Use eq_trans instead\\\")] Notation trans_id := eq_trans (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 467}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem eq_trans : x = y -> y = z -> x = z.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 424}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem eq_trans_r : x = y -> z = y -> x = z.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 431}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"#[deprecated(since=\\\"8.16\\\",note=\\\"Use f_equal instead\\\")] Notation identity_congr := f_equal (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 445}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem f_equal : x = y -> f x = f y.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 436}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"#[deprecated(since=\\\"8.16\\\",note=\\\"Use not_eq_sym instead\\\")] Notation sym_not_id := not_eq_sym (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 469}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem not_eq_sym : x <> y -> y <> x.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 443}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sind_r : forall (A:Type) (x:A) (P:A -> SProp), P x -> forall y:A, y = x -> P y.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 450}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"#[deprecated(since=\\\"8.16\\\",note=\\\"Use eq_ind_r instead\\\")] Notation identity_ind_r := eq_ind_r (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 449}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ind_r : forall (A:Type) (x:A) (P:A -> Prop), P x -> forall y:A, y = x -> P y.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 456}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"#[deprecated(since=\\\"8.16\\\",note=\\\"Use eq_rec_r instead\\\")] Notation identity_rec_r := eq_rec_r (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 451}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_rec_r : forall (A:Type) (x:A) (P:A -> Set), P x -> forall y:A, y = x -> P y.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 463}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"#[deprecated(since=\\\"8.16\\\",note=\\\"Use eq_rect_r instead\\\")] Notation identity_rect_r := eq_rect_r (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 453}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_rect_r : forall (A:Type) (x:A) (P:A -> Type), P x -> forall y:A, y = x -> P y.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 468}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"'rew' H 'in' H'\\\" := (eq_rect _ _ H' _ H) (at level 10, H' at level 10, format \\\"'[' 'rew' H in '/' H' ']'\\\").\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [\"EqNotations\"], \"line\": 475}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"'rew' [ P ] H 'in' H'\\\" := (eq_rect _ P H' _ H) (at level 10, H' at level 10, format \\\"'[' 'rew' [ P ] '/ ' H in '/' H' ']'\\\").\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [\"EqNotations\"], \"line\": 478}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"'rew' <- H 'in' H'\\\" := (eq_rect_r _ H' H) (at level 10, H' at level 10, format \\\"'[' 'rew' <- H in '/' H' ']'\\\").\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [\"EqNotations\"], \"line\": 481}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"'rew' <- [ P ] H 'in' H'\\\" := (eq_rect_r P H' H) (at level 10, H' at level 10, format \\\"'[' 'rew' <- [ P ] '/ ' H in '/' H' ']'\\\").\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [\"EqNotations\"], \"line\": 484}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"'rew' -> H 'in' H'\\\" := (eq_rect _ _ H' _ H) (at level 10, H' at level 10, only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [\"EqNotations\"], \"line\": 487}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"'rew' -> [ P ] H 'in' H'\\\" := (eq_rect _ P H' _ H) (at level 10, H' at level 10, only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [\"EqNotations\"], \"line\": 489}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"'rew' 'dependent' H 'in' H'\\\" := (match H with | eq_refl => H' end) (at level 10, H' at level 10, format \\\"'[' 'rew' 'dependent' '/ ' H in '/' H' ']'\\\").\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [\"EqNotations\"], \"line\": 492}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"'rew' 'dependent' -> H 'in' H'\\\" := (match H with | eq_refl => H' end) (at level 10, H' at level 10, only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [\"EqNotations\"], \"line\": 498}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"'rew' 'dependent' <- H 'in' H'\\\" := (match eq_sym H with | eq_refl => H' end) (at level 10, H' at level 10, format \\\"'[' 'rew' 'dependent' <- '/ ' H in '/' H' ']'\\\").\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [\"EqNotations\"], \"line\": 503}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"'rew' 'dependent' [ 'fun' y p => P ] H 'in' H'\\\" := (match H as p in (_ = y) return P with | eq_refl => H' end) (at level 10, H' at level 10, y name, p name, format \\\"'[' 'rew' 'dependent' [ 'fun' y p => P ] '/ ' H in '/' H' ']'\\\").\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [\"EqNotations\"], \"line\": 509}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"'rew' 'dependent' -> [ 'fun' y p => P ] H 'in' H'\\\" := (match H as p in (_ = y) return P with | eq_refl => H' end) (at level 10, H' at level 10, y name, p name, only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [\"EqNotations\"], \"line\": 515}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"'rew' 'dependent' <- [ 'fun' y p => P ] H 'in' H'\\\" := (match eq_sym H as p in (_ = y) return P with | eq_refl => H' end) (at level 10, H' at level 10, y name, p name, format \\\"'[' 'rew' 'dependent' <- [ 'fun' y p => P ] '/ ' H in '/' H' ']'\\\").\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [\"EqNotations\"], \"line\": 520}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"'rew' 'dependent' [ P ] H 'in' H'\\\" := (match H as p in (_ = y) return P y p with | eq_refl => H' end) (at level 10, H' at level 10, format \\\"'[' 'rew' 'dependent' [ P ] '/ ' H in '/' H' ']'\\\").\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [\"EqNotations\"], \"line\": 526}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"'rew' 'dependent' -> [ P ] H 'in' H'\\\" := (match H as p in (_ = y) return P y p with | eq_refl => H' end) (at level 10, H' at level 10, only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [\"EqNotations\"], \"line\": 532}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"'rew' 'dependent' <- [ P ] H 'in' H'\\\" := (match eq_sym H as p in (_ = y) return P y p with | eq_refl => H' end) (at level 10, H' at level 10, format \\\"'[' 'rew' 'dependent' <- [ P ] '/ ' H in '/' H' ']'\\\").\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [\"EqNotations\"], \"line\": 538}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem f_equal_dep (H: x = y) : rew H in f x = f y.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 554}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma f_equal_dep2 {A A' B B'} (f : A -> A') (g : forall a:A, B a -> B' (f a)) {x1 x2 : A} {y1 : B x1} {y2 : B x2} (H : x1 = x2) : rew H in y1 = y2 -> rew f_equal f H in g x1 y1 = g x2 y2.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 561}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma rew_opp_r A (P:A->Type) (x y:A) (H:x=y) (a:P y) : rew H in rew <- H in a = a.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 568}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma rew_opp_l A (P:A->Type) (x y:A) (H:x=y) (a:P x) : rew <- H in rew H in a = a.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 574}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem f_equal2 : forall (A1 A2 B:Type) (f:A1 -> A2 -> B) (x1 y1:A1) (x2 y2:A2), x1 = y1 -> x2 = y2 -> f x1 x2 = f y1 y2.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 580}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem f_equal3 : forall (A1 A2 A3 B:Type) (f:A1 -> A2 -> A3 -> B) (x1 y1:A1) (x2 y2:A2) (x3 y3:A3), x1 = y1 -> x2 = y2 -> x3 = y3 -> f x1 x2 x3 = f y1 y2 y3.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 589}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem f_equal4 : forall (A1 A2 A3 A4 B:Type) (f:A1 -> A2 -> A3 -> A4 -> B) (x1 y1:A1) (x2 y2:A2) (x3 y3:A3) (x4 y4:A4), x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> f x1 x2 x3 x4 = f y1 y2 y3 y4.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 597}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem f_equal5 : forall (A1 A2 A3 A4 A5 B:Type) (f:A1 -> A2 -> A3 -> A4 -> A5 -> B) (x1 y1:A1) (x2 y2:A2) (x3 y3:A3) (x4 y4:A4) (x5 y5:A5), x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> x5 = y5 -> f x1 x2 x3 x4 x5 = f y1 y2 y3 y4 y5.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 605}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem f_equal_compose A B C (a b:A) (f:A->B) (g:B->C) (e:a=b) : f_equal g (f_equal f e) = f_equal (fun a => g (f a)) e.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 615}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem eq_trans_refl_l A (x y:A) (e:x=y) : eq_trans eq_refl e = e.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 623}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem eq_trans_refl_r A (x y:A) (e:x=y) : eq_trans e eq_refl = e.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 628}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem eq_sym_involutive A (x y:A) (e:x=y) : eq_sym (eq_sym e) = e.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 633}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem eq_trans_sym_inv_l A (x y:A) (e:x=y) : eq_trans (eq_sym e) e = eq_refl.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 638}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem eq_trans_sym_inv_r A (x y:A) (e:x=y) : eq_trans e (eq_sym e) = eq_refl.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 643}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem eq_trans_assoc A (x y z t:A) (e:x=y) (e':y=z) (e'':z=t) : eq_trans e (eq_trans e' e'') = eq_trans (eq_trans e e') e''.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 648}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem rew_map A B (P:B->Type) (f:A->B) x1 x2 (H:x1=x2) (y:P (f x1)) : rew [fun x => P (f x)] H in y = rew f_equal f H in y.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 654}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem eq_trans_map {A B} {x1 x2 x3:A} {y1:B x1} {y2:B x2} {y3:B x3} (H1:x1=x2) (H2:x2=x3) (H1': rew H1 in y1 = y2) (H2': rew H2 in y2 = y3) : rew eq_trans H1 H2 in y1 = y3.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 660}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma map_subst {A} {P Q:A->Type} (f : forall x, P x -> Q x) {x y} (H:x=y) (z:P x) : rew H in f x z = f y (rew H in z).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 667}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma map_subst_map {A B} {P:A->Type} {Q:B->Type} (f:A->B) (g : forall x, P x -> Q (f x)) {x y} (H:x=y) (z:P x) : rew f_equal f H in g x z = g y (rew H in z).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 673}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma rew_swap A (P:A->Type) x1 x2 (H:x1=x2) (y1:P x1) (y2:P x2) : rew H in y1 = y2 -> y1 = rew <- H in y2.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 680}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma rew_compose A (P:A->Type) x1 x2 x3 (H1:x1=x2) (H2:x2=x3) (y:P x1) : rew H2 in rew H1 in y = rew (eq_trans H1 H2) in y.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 685}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem eq_id_comm_l A (f:A->A) (Hf:forall a, a = f a) a : f_equal f (Hf a) = Hf (f a).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 693}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem eq_id_comm_r A (f:A->A) (Hf:forall a, f a = a) a : f_equal f (Hf a) = Hf (f a).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 702}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma eq_refl_map_distr A B x (f:A->B) : f_equal f (eq_refl x) = eq_refl (f x).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 717}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma eq_trans_map_distr A B x y z (f:A->B) (e:x=y) (e':y=z) : f_equal f (eq_trans e e') = eq_trans (f_equal f e) (f_equal f e').\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 722}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma eq_sym_map_distr A B (x y:A) (f:A->B) (e:x=y) : eq_sym (f_equal f e) = f_equal f (eq_sym e).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 728}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma eq_trans_sym_distr A (x y z:A) (e:x=y) (e':y=z) : eq_sym (eq_trans e e') = eq_trans (eq_sym e') (eq_sym e).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 734}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma eq_trans_rew_distr A (P:A -> Type) (x y z:A) (e:x=y) (e':y=z) (k:P x) : rew (eq_trans e e') in k = rew e' in rew e in k.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 740}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma rew_const A P (x y:A) (e:x=y) (k:P) : rew [fun _ => P] e in k = k.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 746}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation sym_eq := eq_sym (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 755}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation trans_eq := eq_trans (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 756}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation sym_not_eq := not_eq_sym (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 757}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation refl_equal := eq_refl (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 759}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation sym_equal := eq_sym (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 760}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation trans_equal := eq_trans (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 761}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation sym_not_equal := not_eq_sym (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 762}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition subrelation (A B : Type) (R R' : A->B->Prop) := forall x y, R x y -> R' x y.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 769}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition unique (A : Type) (P : A->Prop) (x:A) := P x /\\\\ forall (x':A), P x' -> x=x'.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 772}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition uniqueness (A:Type) (P:A->Prop) := forall x y, P x -> P y -> x = y.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 775}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"'exists' ! x .. y , p\\\" := (ex (unique (fun x => .. (ex (unique (fun y => p))) ..))) (at level 200, x binder, right associativity, format \\\"'[' 'exists' ! '/ ' x .. y , '/ ' p ']'\\\") : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 779}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma unique_existence : forall (A:Type) (P:A->Prop), ((exists x, P x) /\\\\ uniqueness P) <-> (exists! x, P x).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 785}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma forall_exists_unique_domain_coincide : forall A (P:A->Prop), (exists! x, P x) -> forall Q:A->Prop, (forall x, P x -> Q x) <-> (exists x, P x /\\\\ Q x).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 797}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma forall_exists_coincide_unique_domain : forall A (P:A->Prop), (forall Q:A->Prop, (forall x, P x -> Q x) <-> (exists x, P x /\\\\ Q x)) -> (exists! x, P x).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 809}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"Inductive inhabited (A:Type) : Prop := inhabits : A -> inhabited A.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 831}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma exists_inhabited : forall (A:Type) (P:A->Prop), (exists x, P x) -> inhabited A.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 836}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma inhabited_covariant (A B : Type) : (A -> B) -> inhabited A -> inhabited B.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 842}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma eq_stepl : forall (A : Type) (x y z : A), x = y -> x = z -> z = y.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 849}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma iff_stepl : forall A B C : Prop, (A <-> B) -> (A <-> C) -> (C <-> B).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 857}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition ex_eta {A : Prop} {P} (p : exists a : A, P a) : p = ex_intro _ (ex_proj1 p) (ex_proj2 p).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 872}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition ex2_eta {A : Prop} {P Q} (p : exists2 a : A, P a & Q a) : p = ex_intro2 _ _ (ex_proj1 (ex_of_ex2 p)) (ex_proj2 (ex_of_ex2 p)) (ex_proj3 p).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 876}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition ex_rect (P0 : ex P -> Type) (f : forall x p, P0 (ex_intro P x p)) : forall e, P0 e := fun e => rew <- ex_eta e in f _ _.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 883}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition ex_rec : forall (P0 : ex P -> Set) (f : forall x p, P0 (ex_intro P x p)), forall e, P0 e := ex_rect.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 886}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition ex_proj1_eq {A : Prop} {P : A -> Prop} {u v : exists a : A, P a} (p : u = v) : ex_proj1 u = ex_proj1 v := f_equal (@ex_proj1 _ _) p.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 896}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition ex_proj2_eq {A : Prop} {P : A -> Prop} {u v : exists a : A, P a} (p : u = v) : rew ex_proj1_eq p in ex_proj2 u = ex_proj2 v := rew dependent p in eq_refl.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 901}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex_intro_uncurried {A : Type} {P : A -> Prop} {u1 v1 : A} {u2 : P u1} {v2 : P v1} (pq : exists p : u1 = v1, rew p in u2 = v2) : ex_intro _ u1 u2 = ex_intro _ v1 v2.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 906}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex_uncurried {A : Prop} {P : A -> Prop} (u v : exists a : A, P a) (pq : exists p : ex_proj1 u = ex_proj1 v, rew p in ex_proj2 u = ex_proj2 v) : u = v.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 916}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex_intro {A : Type} {P : A -> Prop} {u1 v1 : A} {u2 : P u1} {v2 : P v1} (p : u1 = v1) (q : rew p in u2 = v2) : ex_intro _ u1 u2 = ex_intro _ v1 v2 := eq_ex_intro_uncurried (ex_intro _ p q).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 925}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex {A : Prop} {P : A -> Prop} (u v : exists a : A, P a) (p : ex_proj1 u = ex_proj1 v) (q : rew p in ex_proj2 u = ex_proj2 v) : u = v := eq_ex_uncurried u v (ex_intro _ p q).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 931}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex_intro_l {A : Prop} {P : A -> Prop} u1 u2 (v : exists a : A, P a) (p : u1 = ex_proj1 v) (q : rew p in u2 = ex_proj2 v) : ex_intro P u1 u2 = v := eq_ex (ex_intro P u1 u2) v p q.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 939}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex_intro_r {A : Prop} {P : A -> Prop} (u : exists a : A, P a) v1 v2 (p : ex_proj1 u = v1) (q : rew p in ex_proj2 u = v2) : u = ex_intro P v1 v2 := eq_ex u (ex_intro P v1 v2) p q.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 943}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex_eta {A : Prop} {P : A -> Prop} {u v : exists a : A, P a} (p : u = v) : p = eq_ex u v (ex_proj1_eq p) (ex_proj2_eq p).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 949}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex_rect {A : Prop} {P : A -> Prop} {u v : exists a : A, P a} (Q : u = v -> Type) (f : forall p q, Q (eq_ex u v p q)) : forall p, Q p := fun p => rew <- eq_ex_eta p in f _ _.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 951}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex_rec {A : Prop} {P : A -> Prop} {u v} (Q : u = v :> (exists a : A, P a) -> Set) := eq_ex_rect Q.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 955}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex_ind {A : Prop} {P : A -> Prop} {u v} (Q : u = v :> (exists a : A, P a) -> Prop) := eq_ex_rec Q.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 956}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex_rect_ex_intro_l {A : Prop} {P : A -> Prop} {u1 u2 v} (Q : _ -> Type) (f : forall p q, Q (eq_ex_intro_l (P:=P) u1 u2 v p q)) : forall p, Q p := eq_ex_rect Q f.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 961}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex_rect_ex_intro_r {A : Prop} {P : A -> Prop} {u v1 v2} (Q : _ -> Type) (f : forall p q, Q (eq_ex_intro_r (P:=P) u v1 v2 p q)) : forall p, Q p := eq_ex_rect Q f.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 965}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex_rect_ex_intro {A : Prop} {P : A -> Prop} {u1 u2 v1 v2} (Q : _ -> Type) (f : forall p q, Q (@eq_ex_intro A P u1 v1 u2 v2 p q)) : forall p, Q p := eq_ex_rect Q f.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 969}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex_rect_uncurried {A : Prop} {P : A -> Prop} {u v : exists a : A, P a} (Q : u = v -> Type) (f : forall pq, Q (eq_ex u v (ex_proj1 pq) (ex_proj2 pq))) : forall p, Q p := eq_ex_rect Q (fun p q => f (ex_intro _ p q)).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 974}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex_rec_uncurried {A : Prop} {P : A -> Prop} {u v} (Q : u = v :> (exists a : A, P a) -> Set) := eq_ex_rect_uncurried Q.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 978}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex_ind_uncurried {A : Prop} {P : A -> Prop} {u v} (Q : u = v :> (exists a : A, P a) -> Prop) := eq_ex_rec_uncurried Q.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 979}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex_hprop {A : Prop} {P : A -> Prop} (P_hprop : forall (x : A) (p q : P x), p = q) (u v : exists a : A, P a) (p : ex_proj1 u = ex_proj1 v) : u = v := eq_ex u v p (P_hprop _ _ _).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 982}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex_intro_hprop {A : Type} {P : A -> Prop} (P_hprop : forall (x : A) (p q : P x), p = q) {u1 v1 : A} {u2 : P u1} {v2 : P v1} (p : u1 = v1) : ex_intro P u1 u2 = ex_intro P v1 v2 := eq_ex_intro p (P_hprop _ _ _).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 988}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex_uncurried_iff {A : Prop} {P : A -> Prop} (u v : exists a : A, P a) : u = v <-> exists p : ex_proj1 u = ex_proj1 v, rew p in ex_proj2 u = ex_proj2 v.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 997}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex_hprop_iff {A : Prop} {P : A -> Prop} (P_hprop : forall (x : A) (p q : P x), p = q) (u v : exists a : A, P a) : u = v <-> (ex_proj1 u = ex_proj1 v) := conj (fun p => f_equal (@ex_proj1 _ _) p) (eq_ex_hprop P_hprop u v).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 1004}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma rew_ex {A' : Type} {x} {P : A' -> Prop} (Q : forall a, P a -> Prop) (u : exists p : P x, Q x p) {y} (H : x = y) : rew [fun a => exists p : P a, Q a p] H in u = ex_intro (Q y) (rew H in ex_proj1 u) (rew dependent H in ex_proj2 u).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 1009}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition ex2_rect (P0 : ex2 P Q -> Type) (f : forall x p q, P0 (ex_intro2 P Q x p q)) : forall e, P0 e := fun e => rew <- ex2_eta e in f _ _ _.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 1024}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition ex2_rec : forall (P0 : ex2 P Q -> Set) (f : forall x p q, P0 (ex_intro2 P Q x p q)), forall e, P0 e := ex2_rect.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 1027}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition ex_of_ex2_eq {A : Prop} {P Q : A -> Prop} {u v : exists2 a : A, P a & Q a} (p : u = v) : u = v :> exists a : A, P a := f_equal _ p.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 1039}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition ex_proj1_of_ex2_eq {A : Prop} {P Q : A -> Prop} {u v : exists2 a : A, P a & Q a} (p : u = v) : ex_proj1 u = ex_proj1 v := ex_proj1_eq (ex_of_ex2_eq p).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 1042}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition ex_proj2_of_ex2_eq {A : Prop} {P Q : A -> Prop} {u v : exists2 a : A, P a & Q a} (p : u = v) : rew ex_proj1_of_ex2_eq p in ex_proj2 u = ex_proj2 v := rew dependent p in eq_refl.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 1047}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition ex_proj3_eq {A : Prop} {P Q : A -> Prop} {u v : exists2 a : A, P a & Q a} (p : u = v) : rew ex_proj1_of_ex2_eq p in ex_proj3 u = ex_proj3 v := rew dependent p in eq_refl.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 1052}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex_intro2_uncurried {A : Type} {P Q : A -> Prop} {u1 v1 : A} {u2 : P u1} {v2 : P v1} {u3 : Q u1} {v3 : Q v1} (pqr : exists2 p : u1 = v1, rew p in u2 = v2 & rew p in u3 = v3) : ex_intro2 _ _ u1 u2 u3 = ex_intro2 _ _ v1 v2 v3.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 1057}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex2_uncurried {A : Prop} {P Q : A -> Prop} (u v : exists2 a : A, P a & Q a) (pqr : exists2 p : ex_proj1 u = ex_proj1 v, rew p in ex_proj2 u = ex_proj2 v & rew p in ex_proj3 u = ex_proj3 v) : u = v.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 1067}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex2 {A : Prop} {P Q : A -> Prop} (u v : exists2 a : A, P a & Q a) (p : ex_proj1 u = ex_proj1 v) (q : rew p in ex_proj2 u = ex_proj2 v) (r : rew p in ex_proj3 u = ex_proj3 v) : u = v := eq_ex2_uncurried u v (ex_intro2 _ _ p q r).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 1077}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex_intro2 {A : Type} {P Q : A -> Prop} {u1 v1 : A} {u2 : P u1} {v2 : P v1} {u3 : Q u1} {v3 : Q v1} (p : u1 = v1) (q : rew p in u2 = v2) (r : rew p in u3 = v3) : ex_intro2 P Q u1 u2 u3 = ex_intro2 P Q v1 v2 v3 := eq_ex_intro2_uncurried (ex_intro2 _ _ p q r).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 1084}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex_intro2_l {A : Prop} {P Q : A -> Prop} u1 u2 u3 (v : exists2 a : A, P a & Q a) (p : u1 = ex_proj1 v) (q : rew p in u2 = ex_proj2 v) (r : rew p in u3 = ex_proj3 v) : ex_intro2 P Q u1 u2 u3 = v := eq_ex2 (ex_intro2 P Q u1 u2 u3) v p q r.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 1094}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex_intro2_r {A : Prop} {P Q : A -> Prop} (u : exists2 a : A, P a & Q a) v1 v2 v3 (p : ex_proj1 u = v1) (q : rew p in ex_proj2 u = v2) (r : rew p in ex_proj3 u = v3) : u = ex_intro2 P Q v1 v2 v3 := eq_ex2 u (ex_intro2 P Q v1 v2 v3) p q r.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 1098}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex2_hprop {A : Prop} {P Q : A -> Prop} (Q_hprop : forall (x : A) (p q : Q x), p = q) (u v : exists2 a : A, P a & Q a) (p : u = v :> exists a : A, P a) : u = v := eq_ex2 u v (ex_proj1_eq p) (ex_proj2_eq p) (Q_hprop _ _ _).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 1104}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex_intro2_hprop_nondep {A : Type} {P : A -> Prop} {Q : Prop} (Q_hprop : forall (p q : Q), p = q) {u1 v1 : A} {u2 : P u1} {v2 : P v1} {u3 v3 : Q} (p : ex_intro _ u1 u2 = ex_intro _ v1 v2) : ex_intro2 _ _ u1 u2 u3 = ex_intro2 _ _ v1 v2 v3 := rew [fun v3 => _ = ex_intro2 _ _ _ _ v3] (Q_hprop u3 v3) in f_equal (fun u => match u with ex_intro _ u1 u2 => ex_intro2 _ _ u1 u2 u3 end) p.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 1110}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex_intro2_hprop {A : Type} {P Q : A -> Prop} (P_hprop : forall x (p q : P x), p = q) (Q_hprop : forall x (p q : Q x), p = q) {u1 v1 : A} {u2 : P u1} {v2 : P v1} {u3 : Q u1} {v3 : Q v1} (p : u1 = v1) : ex_intro2 P Q u1 u2 u3 = ex_intro2 P Q v1 v2 v3 := eq_ex_intro2 p (P_hprop _ _ _) (Q_hprop _ _ _).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 1117}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex2_uncurried_iff {A : Prop} {P Q : A -> Prop} (u v : exists2 a : A, P a & Q a) : u = v <-> exists2 p : ex_proj1 u = ex_proj1 v, rew p in ex_proj2 u = ex_proj2 v & rew p in ex_proj3 u = ex_proj3 v.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 1128}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex2_eta {A : Prop} {P Q : A -> Prop} {u v : exists2 a : A, P a & Q a} (p : u = v) : p = eq_ex2 u v (ex_proj1_of_ex2_eq p) (ex_proj2_of_ex2_eq p) (ex_proj3_eq p).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 1137}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex2_rect {A : Prop} {P Q : A -> Prop} {u v : exists2 a : A, P a & Q a} (R : u = v -> Type) (f : forall p q r, R (eq_ex2 u v p q r)) : forall p, R p := fun p => rew <- eq_ex2_eta p in f _ _ _.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 1140}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex2_rec {A : Prop} {P Q : A -> Prop} {u v} (R : u = v :> (exists2 a : A, P a & Q a) -> Set) := eq_ex2_rect R.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 1144}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex2_ind {A : Prop} {P Q : A -> Prop} {u v} (R : u = v :> (exists2 a : A, P a & Q a) -> Prop) := eq_ex2_rec R.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 1145}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex2_rect_ex_intro2_l {A : Prop} {P Q : A -> Prop} {u1 u2 u3 v} (R : _ -> Type) (f : forall p q r, R (eq_ex_intro2_l (P:=P) (Q:=Q) u1 u2 u3 v p q r)) : forall p, R p := eq_ex2_rect R f.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 1150}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex2_rect_ex_intro2_r {A : Prop} {P Q : A -> Prop} {u v1 v2 v3} (R : _ -> Type) (f : forall p q r, R (eq_ex_intro2_r (P:=P) (Q:=Q) u v1 v2 v3 p q r)) : forall p, R p := eq_ex2_rect R f.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 1154}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex2_rect_ex_intro2 {A : Prop} {P Q : A -> Prop} {u1 u2 u3 v1 v2 v3} (R : _ -> Type) (f : forall p q r, R (@eq_ex_intro2 A P Q u1 v1 u2 v2 u3 v3 p q r)) : forall p, R p := eq_ex2_rect R f.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 1158}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex2_rect_uncurried {A : Prop} {P Q : A -> Prop} {u v : exists2 a : A, P a & Q a} (R : u = v -> Type) (f : forall pqr : exists2 p : _ = _, _ & _, R (eq_ex2 u v (ex_proj1 pqr) (ex_proj2 pqr) (ex_proj3 pqr))) : forall p, R p := eq_ex2_rect R (fun p q r => f (ex_intro2 _ _ p q r)).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 1163}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex2_rec_uncurried {A : Prop} {P Q : A -> Prop} {u v} (R : u = v :> (exists2 a : A, P a & Q a) -> Set) := eq_ex2_rect_uncurried R.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 1167}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex2_ind_uncurried {A : Prop} {P Q : A -> Prop} {u v} (R : u = v :> (exists2 a : A, P a & Q a) -> Prop) := eq_ex2_rec_uncurried R.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 1168}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex2_hprop_iff {A : Prop} {P Q : A -> Prop} (Q_hprop : forall (x : A) (p q : Q x), p = q) (u v : exists2 a : A, P a & Q a) : u = v <-> (u = v :> exists a : A, P a) := conj (fun p => f_equal (@ex_of_ex2 _ _ _) p) (eq_ex2_hprop Q_hprop u v).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 1171}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_ex2_nondep {A : Prop} {B C : Prop} (u v : @ex2 A (fun _ => B) (fun _ => C)) (p : ex_proj1 u = ex_proj1 v) (q : ex_proj2 u = ex_proj2 v) (r : ex_proj3 u = ex_proj3 v) : u = v := @eq_ex2 _ _ _ u v p (eq_trans (rew_const _ _) q) (eq_trans (rew_const _ _) r).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 1177}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma rew_ex2 {A' : Type} {x} {P : A' -> Prop} (Q R : forall a, P a -> Prop) (u : exists2 p : P x, Q x p & R x p) {y} (H : x = y) : rew [fun a => exists2 p : P a, Q a p & R a p] H in u = ex_intro2 (Q y) (R y) (rew H in ex_proj1 u) (rew dependent H in ex_proj2 u) (rew dependent H in ex_proj3 u).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Logic.v\", \"module\": [], \"line\": 1183}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"Inductive Empty_set : Set :=.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 21}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"Inductive unit : Set := tt : unit.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 27}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"Inductive bool : Set := | true : bool | false : bool.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 38}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition andb (b1 b2:bool) : bool := if b1 then b2 else false.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 54}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition orb (b1 b2:bool) : bool := if b1 then true else b2.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 56}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition implb (b1 b2:bool) : bool := if b1 then b2 else true.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 58}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition xorb (b1 b2:bool) : bool := if b1 then if b2 then false else true else b2.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 60}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition negb (b:bool) := if b then false else true.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 65}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Infix \\\"||\\\" := orb : bool_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 67}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Infix \\\"&&\\\" := andb : bool_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 68}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma andb_prop (a b:bool) : andb a b = true -> a = true /\\\\ b = true.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 78}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma andb_true_intro (b1 b2:bool) : b1 = true /\\\\ b2 = true -> andb b1 b2 = true.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 87}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"Inductive eq_true : bool -> Prop := is_eq_true : eq_true true.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 99}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition is_true b := b = true.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 108}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma eq_true_ind_r : forall (P : bool -> Prop) (b : bool), P b -> eq_true b -> P true.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 116}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma eq_true_rec_r : forall (P : bool -> Set) (b : bool), P b -> eq_true b -> P true.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 122}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma eq_true_rect_r : forall (P : bool -> Type) (b : bool), P b -> eq_true b -> P true.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 128}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"Inductive BoolSpec (P Q : Prop) : bool -> Prop := | BoolSpecT : P -> BoolSpec P Q true | BoolSpecF : Q -> BoolSpec P Q false.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 141}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"Inductive nat : Set := | O : nat | S : nat -> nat.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 159}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"#[universes(template)] Inductive option (A:Type) : Type := | Some : A -> option A | None : option A.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 182}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition option_map (A B:Type) (f:A->B) (o : option A) : option B := match o with | Some a => @Some B (f a) | None => @None B end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 194}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"#[universes(template)] Inductive sum (A B:Type) : Type := | inl : A -> sum A B | inr : B -> sum A B.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 202}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"x + y\\\" := (sum x y) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 207}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"#[universes(template)] Inductive prod (A B:Type) : Type := pair : A -> B -> A * B where \\\"x * y\\\" := (prod x y) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 219}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"#[universes(template)] Inductive prod (A B:Type) : Type := pair : A -> B -> A * B where \\\"x * y\\\" := (prod x y) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 219}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"( x , y , .. , z )\\\" := (pair .. (pair x y) .. z) : core_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 227}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition fst (p:A * B) := match p with (x, y) => x end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 238}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition snd (p:A * B) := match p with (x, y) => y end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 239}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma surjective_pairing (A B:Type) (p:A * B) : p = (fst p, snd p).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 249}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma injective_projections (A B:Type) (p1 p2:A * B) : fst p1 = fst p2 -> snd p1 = snd p2 -> p1 = p2.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 254}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma pair_equal_spec (A B : Type) (a1 a2 : A) (b1 b2 : B) : (a1, b1) = (a2, b2) <-> a1 = a2 /\\\\ b1 = b2.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 261}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition curry {A B C:Type} (f:A * B -> C) (x:A) (y:B) : C := f (x,y).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 273}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition uncurry {A B C:Type} (f:A -> B -> C) (p:A * B) : C := match p with (x, y) => f x y end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 276}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma rew_pair A (P Q : A->Type) x1 x2 (y1:P x1) (y2:Q x1) (H:x1=x2) : (rew H in y1, rew H in y2) = rew [fun x => (P x * Q x)%type] H in (y1,y2).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 281}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"#[universes(template)] Inductive list (A : Type) : Type := | nil : list A | cons : A -> list A -> list A.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 289}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Infix \\\"::\\\" := cons (at level 60, right associativity) : list_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 301}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition length (A : Type) : list A -> nat := fix length l := match l with | nil => O | _ :: l' => S (length l') end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 309}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition app d d' := revapp (rev d) d'.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Hexadecimal.v\", \"module\": [], \"line\": 164}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition app (A : Type) : list A -> list A -> list A := fix app l m := match l with | nil => m | a :: l1 => a :: app l1 m end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 318}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Infix \\\"++\\\" := app (right associativity, at level 60) : list_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 325}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"Inductive comparison : Set := | Eq : comparison | Lt : comparison | Gt : comparison.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 332}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma comparison_eq_stable (c c' : comparison) : ~~ c = c' -> c = c'.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 342}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition CompOpp (r:comparison) := match r with | Eq => Eq | Lt => Gt | Gt => Lt end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 347}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma CompOpp_involutive c : CompOpp (CompOpp c) = c.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 354}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma CompOpp_inj c c' : CompOpp c = CompOpp c' -> c = c'.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 359}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma CompOpp_iff : forall c c', CompOpp c = c' <-> c = CompOpp c'.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 364}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"Inductive CompareSpec (Peq Plt Pgt : Prop) : comparison -> Prop := | CompEq : Peq -> CompareSpec Peq Plt Pgt Eq | CompLt : Plt -> CompareSpec Peq Plt Pgt Lt | CompGt : Pgt -> CompareSpec Peq Plt Pgt Gt.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 374}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"Inductive CompareSpecT (Peq Plt Pgt : Prop) : comparison -> Type := | CompEqT : Peq -> CompareSpecT Peq Plt Pgt Eq | CompLtT : Plt -> CompareSpecT Peq Plt Pgt Lt | CompGtT : Pgt -> CompareSpecT Peq Plt Pgt Gt.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 390}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma CompareSpec2Type Peq Plt Pgt c : CompareSpec Peq Plt Pgt c -> CompareSpecT Peq Plt Pgt c.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 402}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition CompSpec {A} (eq lt : A->A->Prop)(x y:A) : comparison -> Prop := CompareSpec (eq x y) (lt x y) (lt y x).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 412}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition CompSpecT {A} (eq lt : A->A->Prop)(x y:A) : comparison -> Type := CompareSpecT (eq x y) (lt x y) (lt y x).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 415}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma CompSpec2Type : forall A (eq lt:A->A->Prop) x y c, CompSpec eq lt x y c -> CompSpecT eq lt x y c.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 420}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"#[deprecated(since=\\\"8.16\\\",note=\\\"Use eq_ind instead\\\")] Notation identity_ind := eq_ind (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 435}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"#[deprecated(since=\\\"8.16\\\",note=\\\"Use eq_rec instead\\\")] Notation identity_rec := eq_rec (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 437}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"#[deprecated(since=\\\"8.16\\\",note=\\\"Use eq_rect instead\\\")] Notation identity_rect := eq_rect (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 439}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition ID := forall A:Type, A -> A.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 474}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition id : ID := fun A x => x.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 475}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition IDProp := forall A:Prop, A -> A.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 477}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition idProp : IDProp := fun A x => x.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 478}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation prodT := prod (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 486}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation pairT := pair (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 487}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation prodT_rect := prod_rect (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 488}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation prodT_rec := prod_rec (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 489}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation prodT_ind := prod_ind (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 490}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation fstT := fst (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 491}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation sndT := snd (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Datatypes.v\", \"module\": [], \"line\": 492}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"#[universes(template)] Inductive sig (A:Type) (P:A -> Prop) : Type := exist : forall x:A, P x -> sig P.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 27}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"#[universes(template)] Inductive sig2 (A:Type) (P Q:A -> Prop) : Type := exist2 : forall x:A, P x -> Q x -> sig2 P Q.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 35}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"#[universes(template)] Inductive sigT (A:Type) (P:A -> Type) : Type := existT : forall x:A, P x -> sigT P.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 42}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"#[universes(template)] Inductive sigT2 (A:Type) (P Q:A -> Type) : Type := existT2 : forall x:A, P x -> Q x -> sigT2 P Q.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 50}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"{ x | P }\\\" := (sig (fun x => P)) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 61}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"{ x | P & Q }\\\" := (sig2 (fun x => P) (fun x => Q)) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 62}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"{ x : A | P }\\\" := (sig (A:=A) (fun x => P)) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 63}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"{ x : A | P & Q }\\\" := (sig2 (A:=A) (fun x => P) (fun x => Q)) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 64}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"{ x & P }\\\" := (sigT (fun x => P)) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 66}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"{ x & P & Q }\\\" := (sigT2 (fun x => P) (fun x => Q)) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 67}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"{ x : A & P }\\\" := (sigT (A:=A) (fun x => P)) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 68}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"{ x : A & P & Q }\\\" := (sigT2 (A:=A) (fun x => P) (fun x => Q)) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 69}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"{ ' pat | P }\\\" := (sig (fun pat => P)) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 72}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"{ ' pat | P & Q }\\\" := (sig2 (fun pat => P) (fun pat => Q)) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 73}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"{ ' pat : A | P }\\\" := (sig (A:=A) (fun pat => P)) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 74}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"{ ' pat : A | P & Q }\\\" := (sig2 (A:=A) (fun pat => P) (fun pat => Q)) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 75}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"{ ' pat & P }\\\" := (sigT (fun pat => P)) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 77}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"{ ' pat & P & Q }\\\" := (sigT2 (fun pat => P) (fun pat => Q)) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 78}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"{ ' pat : A & P }\\\" := (sigT (A:=A) (fun pat => P)) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 79}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"{ ' pat : A & P & Q }\\\" := (sigT2 (A:=A) (fun pat => P) (fun pat => Q)) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 80}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition proj1_sig (e:sig P) := match e with | exist _ a b => a end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 102}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition proj2_sig (e:sig P) := match e return P (proj1_sig e) with | exist _ a b => b end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 106}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition sig_of_sig2 (A : Type) (P Q : A -> Prop) (X : sig2 P Q) : sig P := exist P (let (a, _, _) := X in a) (let (x, p, _) as s return (P (let (a, _, _) := s in a)) := X in p).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 125}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition proj3_sig (e : sig2 P Q) := let (a, b, c) return Q (proj1_sig (sig_of_sig2 e)) := e in c.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 144}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition projT1 (x:sigT P) : A := match x with | existT _ a _ => a end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 164}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition projT2 (x:sigT P) : P (projT1 x) := match x return P (projT1 x) with | existT _ _ h => h end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 168}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"( x ; y )\\\" := (existT _ x y) (at level 0, format \\\"( x ; '/ ' y )\\\").\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [\"SigTNotations\"], \"line\": 179}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"x .1\\\" := (projT1 x) (at level 1, left associativity, format \\\"x .1\\\").\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [\"SigTNotations\"], \"line\": 180}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"x .2\\\" := (projT2 x) (at level 1, left associativity, format \\\"x .2\\\").\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [\"SigTNotations\"], \"line\": 181}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition sigT_of_sigT2 (A : Type) (P Q : A -> Type) (X : sigT2 P Q) : sigT P := existT P (let (a, _, _) := X in a) (let (x, p, _) as s return (P (let (a, _, _) := s in a)) := X in p).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 194}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition projT3 (e : sigT2 P Q) := let (a, b, c) return Q (projT1 (sigT_of_sigT2 e)) := e in c.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 213}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition sig_of_sigT (A : Type) (P : A -> Prop) (X : sigT P) : sig P := exist P (projT1 X) (projT2 X).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 222}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition sigT_of_sig (A : Type) (P : A -> Prop) (X : sig P) : sigT P := existT P (proj1_sig X) (proj2_sig X).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 225}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition sig2_of_sigT2 (A : Type) (P Q : A -> Prop) (X : sigT2 P Q) : sig2 P Q := exist2 P Q (projT1 (sigT_of_sigT2 X)) (projT2 (sigT_of_sigT2 X)) (projT3 X).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 230}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition sigT2_of_sig2 (A : Type) (P Q : A -> Prop) (X : sig2 P Q) : sigT2 P Q := existT2 P Q (proj1_sig (sig_of_sig2 X)) (proj2_sig (sig_of_sig2 X)) (proj3_sig X).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 233}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition ex_of_sig (A : Type) (P : A -> Prop) (X : sig P) : ex P := ex_intro P (proj1_sig X) (proj2_sig X).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 238}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition ex_of_sigT (A : Type) (P : A -> Prop) (X : sigT P) : ex P := ex_of_sig (sig_of_sigT X).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 243}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition ex2_of_sig2 (A : Type) (P Q : A -> Prop) (X : sig2 P Q) : ex2 P Q := ex_intro2 P Q (proj1_sig (sig_of_sig2 X)) (proj2_sig (sig_of_sig2 X)) (proj3_sig X).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 248}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition ex2_of_sigT2 (A : Type) (P Q : A -> Prop) (X : sigT2 P Q) : ex2 P Q := ex2_of_sig2 (sig2_of_sigT2 X).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 253}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition sigT_eta {A P} (p : { a : A & P a }) : p = existT _ (projT1 p) (projT2 p).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 257}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition sig_eta {A P} (p : { a : A | P a }) : p = exist _ (proj1_sig p) (proj2_sig p).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 261}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition sigT2_eta {A P Q} (p : { a : A & P a & Q a }) : p = existT2 _ _ (projT1 (sigT_of_sigT2 p)) (projT2 (sigT_of_sigT2 p)) (projT3 p).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 265}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition sig2_eta {A P Q} (p : { a : A | P a & Q a }) : p = exist2 _ _ (proj1_sig (sig_of_sig2 p)) (proj2_sig (sig_of_sig2 p)) (proj3_sig p).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 269}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma exists_to_inhabited_sig {A P} : (exists x : A, P x) -> inhabited {x : A | P x}.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 274}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma inhabited_sig_to_exists {A P} : inhabited {x : A | P x} -> exists x : A, P x.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 279}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition sigT_of_prod (p : A * B) := (fst p; snd p).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 290}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition prod_of_sigT (s : { _ : A & B }) := (s.1, s.2).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 291}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma sigT_prod_sigT p : sigT_of_prod (prod_of_sigT p) = p.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 293}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma prod_sigT_prod s : prod_of_sigT (sigT_of_prod s) = s.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 296}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition projT1_eq {A} {P : A -> Type} {u v : { a : A & P a }} (p : u = v) : u.1 = v.1 := f_equal (fun x => x.1) p.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 309}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition projT2_eq {A} {P : A -> Type} {u v : { a : A & P a }} (p : u = v) : rew projT1_eq p in u.2 = v.2 := rew dependent p in eq_refl.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 314}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_existT_uncurried {A : Type} {P : A -> Type} {u1 v1 : A} {u2 : P u1} {v2 : P v1} (pq : { p : u1 = v1 & rew p in u2 = v2 }) : (u1; u2) = (v1; v2).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 319}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sigT_uncurried {A : Type} {P : A -> Type} (u v : { a : A & P a }) (pq : { p : u.1 = v.1 & rew p in u.2 = v.2 }) : u = v.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 329}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma eq_existT_curried {A : Type} {P : A -> Type} {u1 v1 : A} {u2 : P u1} {v2 : P v1} (p : u1 = v1) (q : rew p in u2 = v2) : (u1; u2) = (v1; v2).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 337}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma eq_existT_curried_map {A A' P P'} (f:A -> A') (g:forall u:A, P u -> P' (f u)) {u1 v1 : A} {u2 : P u1} {v2 : P v1} (p : u1 = v1) (q : rew p in u2 = v2) : f_equal (fun x => (f x.1; g x.1 x.2)) (= p; q) = (= f_equal f p; f_equal_dep2 f g p q).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 345}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma eq_existT_curried_trans {A P} {u1 v1 w1 : A} {u2 : P u1} {v2 : P v1} {w2 : P w1} (p : u1 = v1) (q : rew p in u2 = v2) (p' : v1 = w1) (q': rew p' in v2 = w2) : eq_trans (= p; q) (= p'; q') = (= eq_trans p p'; eq_trans_map p p' q q').\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 353}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem eq_existT_curried_congr {A P} {u1 v1 : A} {u2 : P u1} {v2 : P v1} {p p' : u1 = v1} {q : rew p in u2 = v2} {q': rew p' in u2 = v2} (r : p = p') : rew [fun H => rew H in u2 = v2] r in q = q' -> (= p; q) = (= p'; q').\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 362}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sigT {A : Type} {P : A -> Type} (u v : { a : A & P a }) (p : u.1 = v.1) (q : rew p in u.2 = v.2) : u = v := eq_sigT_uncurried u v (existT _ p q).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 370}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_existT_l {A : Type} {P : A -> Type} {u1 : A} {u2 : P u1} {v : { a : A & P a }} (p : u1 = v.1) (q : rew p in u2 = v.2) : (u1; u2) = v := eq_sigT (u1; u2) v p q.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 378}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_existT_r {A : Type} {P : A -> Type} {u : { a : A & P a }} {v1 : A} {v2 : P v1} (p : u.1 = v1) (q : rew p in u.2 = v2) : u = (v1; v2) := eq_sigT u (v1; v2) p q.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 381}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sigT_hprop {A P} (P_hprop : forall (x : A) (p q : P x), p = q) (u v : { a : A & P a }) (p : u.1 = v.1) : u = v := eq_sigT u v p (P_hprop _ _ _).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 386}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sigT_uncurried_iff {A P} (u v : { a : A & P a }) : u = v <-> { p : u.1 = v.1 & rew p in u.2 = v.2 }.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 395}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sigT_rect {A P} {u v : { a : A & P a }} (Q : u = v -> Type) (f : forall p q, Q (eq_sigT u v p q)) : forall p, Q p.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 403}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sigT_rec {A P u v} (Q : u = v :> { a : A & P a } -> Set) := eq_sigT_rect Q.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 407}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sigT_ind {A P u v} (Q : u = v :> { a : A & P a } -> Prop) := eq_sigT_rec Q.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 408}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sigT_rect_existT_l {A P} {u1 u2 v} (Q : _ -> Type) (f : forall p q, Q (@eq_existT_l A P u1 u2 v p q)) : forall p, Q p := eq_sigT_rect Q f.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 413}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sigT_rect_existT_r {A P} {u v1 v2} (Q : _ -> Type) (f : forall p q, Q (@eq_existT_r A P u v1 v2 p q)) : forall p, Q p := eq_sigT_rect Q f.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 417}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sigT_rect_existT {A P} {u1 u2 v1 v2} (Q : _ -> Type) (f : forall p q, Q (@eq_existT_curried A P u1 v1 u2 v2 p q)) : forall p, Q p := eq_sigT_rect Q f.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 421}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sigT_rect_uncurried {A P} {u v : { a : A & P a }} (Q : u = v -> Type) (f : forall pq : exists p : u.1 = v.1, _, Q (eq_sigT u v (ex_proj1 pq) (ex_proj2 pq))) : forall p, Q p := eq_sigT_rect Q (fun p q => f (ex_intro _ p q)).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 430}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sigT_rec_uncurried {A P u v} (Q : u = v :> { a : A & P a } -> Set) := eq_sigT_rect_uncurried Q.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 434}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sigT_ind_uncurried {A P u v} (Q : u = v :> { a : A & P a } -> Prop) := eq_sigT_rec_uncurried Q.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 435}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sigT_hprop_iff {A P} (P_hprop : forall (x : A) (p q : P x), p = q) (u v : { a : A & P a }) : u = v <-> (u.1 = v.1) := conj (fun p => f_equal (@projT1 _ _) p) (eq_sigT_hprop P_hprop u v).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 438}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sigT_nondep {A B : Type} (u v : { a : A & B }) (p : u.1 = v.1) (q : u.2 = v.2) : u = v := @eq_sigT _ _ u v p (eq_trans (rew_const _ _) q).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 444}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma rew_sigT {A x} {P : A -> Type} (Q : forall a, P a -> Prop) (u : { p : P x & Q x p }) {y} (H : x = y) : rew [fun a => { p : P a & Q a p }] H in u = existT (Q y) (rew H in u.1) (rew dependent H in (u.2)).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 450}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition proj1_sig_eq {A} {P : A -> Prop} {u v : { a : A | P a }} (p : u = v) : proj1_sig u = proj1_sig v := f_equal (@proj1_sig _ _) p.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 469}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition proj2_sig_eq {A} {P : A -> Prop} {u v : { a : A | P a }} (p : u = v) : rew proj1_sig_eq p in proj2_sig u = proj2_sig v := rew dependent p in eq_refl.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 474}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_exist_uncurried {A : Type} {P : A -> Prop} {u1 v1 : A} {u2 : P u1} {v2 : P v1} (pq : { p : u1 = v1 | rew p in u2 = v2 }) : exist _ u1 u2 = exist _ v1 v2.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 479}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sig_uncurried {A : Type} {P : A -> Prop} (u v : { a : A | P a }) (pq : { p : proj1_sig u = proj1_sig v | rew p in proj2_sig u = proj2_sig v }) : u = v.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 489}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma eq_exist_curried {A : Type} {P : A -> Prop} {u1 v1 : A} {u2 : P u1} {v2 : P v1} (p : u1 = v1) (q : rew p in u2 = v2) : exist P u1 u2 = exist P v1 v2.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 497}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sig {A : Type} {P : A -> Prop} (u v : { a : A | P a }) (p : proj1_sig u = proj1_sig v) (q : rew p in proj2_sig u = proj2_sig v) : u = v := eq_sig_uncurried u v (exist _ p q).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 504}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_exist_l {A : Type} {P : A -> Prop} {u1 : A} {u2 : P u1} {v : { a : A | P a }} (p : u1 = proj1_sig v) (q : rew p in u2 = proj2_sig v) : exist _ u1 u2 = v := eq_sig (exist _ u1 u2) v p q.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 512}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_exist_r {A : Type} {P : A -> Prop} {u : { a : A | P a }} {v1 : A} {v2 : P v1} (p : proj1_sig u = v1) (q : rew p in proj2_sig u = v2) : u = exist _ v1 v2 := eq_sig u (exist _ v1 v2) p q.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 515}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sig_rect {A P} {u v : { a : A | P a }} (Q : u = v -> Type) (f : forall p q, Q (eq_sig u v p q)) : forall p, Q p.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 520}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sig_rec {A P u v} (Q : u = v :> { a : A | P a } -> Set) := eq_sig_rect Q.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 524}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sig_ind {A P u v} (Q : u = v :> { a : A | P a } -> Prop) := eq_sig_rec Q.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 525}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sig_rect_exist_l {A P} {u1 u2 v} (Q : _ -> Type) (f : forall p q, Q (@eq_exist_l A P u1 u2 v p q)) : forall p, Q p := eq_sig_rect Q f.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 530}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sig_rect_exist_r {A P} {u v1 v2} (Q : _ -> Type) (f : forall p q, Q (@eq_exist_r A P u v1 v2 p q)) : forall p, Q p := eq_sig_rect Q f.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 534}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sig_rect_exist {A P} {u1 u2 v1 v2} (Q : _ -> Type) (f : forall p q, Q (@eq_exist_curried A P u1 v1 u2 v2 p q)) : forall p, Q p := eq_sig_rect Q f.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 538}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sig_rect_uncurried {A P} {u v : { a : A | P a }} (Q : u = v -> Type) (f : forall pq : exists p : proj1_sig u = proj1_sig v, _, Q (eq_sig u v (ex_proj1 pq) (ex_proj2 pq))) : forall p, Q p := eq_sig_rect Q (fun p q => f (ex_intro _ p q)).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 547}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sig_rec_uncurried {A P u v} (Q : u = v :> { a : A | P a } -> Set) := eq_sig_rect_uncurried Q.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 551}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sig_ind_uncurried {A P u v} (Q : u = v :> { a : A | P a } -> Prop) := eq_sig_rec_uncurried Q.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 552}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sig_hprop {A} {P : A -> Prop} (P_hprop : forall (x : A) (p q : P x), p = q) (u v : { a : A | P a }) (p : proj1_sig u = proj1_sig v) : u = v := eq_sig u v p (P_hprop _ _ _).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 555}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sig_uncurried_iff {A} {P : A -> Prop} (u v : { a : A | P a }) : u = v <-> { p : proj1_sig u = proj1_sig v | rew p in proj2_sig u = proj2_sig v }.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 564}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sig_hprop_iff {A} {P : A -> Prop} (P_hprop : forall (x : A) (p q : P x), p = q) (u v : { a : A | P a }) : u = v <-> (proj1_sig u = proj1_sig v) := conj (fun p => f_equal (@proj1_sig _ _) p) (eq_sig_hprop P_hprop u v).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 572}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma rew_sig {A x} {P : A -> Type} (Q : forall a, P a -> Prop) (u : { p : P x | Q x p }) {y} (H : x = y) : rew [fun a => { p : P a | Q a p }] H in u = exist (Q y) (rew H in proj1_sig u) (rew dependent H in proj2_sig u).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 577}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition sigT_of_sigT2_eq {A} {P Q : A -> Type} {u v : { a : A & P a & Q a }} (p : u = v) : u = v :> { a : A & P a } := f_equal _ p.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 596}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition projT1_of_sigT2_eq {A} {P Q : A -> Type} {u v : { a : A & P a & Q a }} (p : u = v) : u.1 = v.1 := projT1_eq (sigT_of_sigT2_eq p).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 599}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition projT2_of_sigT2_eq {A} {P Q : A -> Type} {u v : { a : A & P a & Q a }} (p : u = v) : rew projT1_of_sigT2_eq p in u.2 = v.2 := rew dependent p in eq_refl.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 604}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition projT3_eq {A} {P Q : A -> Type} {u v : { a : A & P a & Q a }} (p : u = v) : rew projT1_of_sigT2_eq p in u.3 = v.3 := rew dependent p in eq_refl.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 609}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_existT2_uncurried {A : Type} {P Q : A -> Type} {u1 v1 : A} {u2 : P u1} {v2 : P v1} {u3 : Q u1} {v3 : Q v1} (pqr : { p : u1 = v1 & rew p in u2 = v2 & rew p in u3 = v3 }) : existT2 _ _ u1 u2 u3 = existT2 _ _ v1 v2 v3.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 614}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sigT2_uncurried {A : Type} {P Q : A -> Type} (u v : { a : A & P a & Q a }) (pqr : { p : u.1 = v.1 & rew p in u.2 = v.2 & rew p in u.3 = v.3 }) : u = v.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 626}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma eq_existT2_curried {A : Type} {P Q : A -> Type} {u1 v1 : A} {u2 : P u1} {v2 : P v1} {u3 : Q u1} {v3 : Q v1} (p : u1 = v1) (q : rew p in u2 = v2) (r : rew p in u3 = v3) : existT2 P Q u1 u2 u3 = existT2 P Q v1 v2 v3.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 635}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sigT2 {A : Type} {P Q : A -> Type} (u v : { a : A & P a & Q a }) (p : u.1 = v.1) (q : rew p in u.2 = v.2) (r : rew p in u.3 = v.3) : u = v := eq_sigT2_uncurried u v (existT2 _ _ p q r).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 642}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_existT2_l {A : Type} {P Q : A -> Type} {u1 : A} {u2 : P u1} {u3 : Q u1} {v : { a : A & P a & Q a }} (p : u1 = v.1) (q : rew p in u2 = v.2) (r : rew p in u3 = v.3) : existT2 P Q u1 u2 u3 = v := eq_sigT2 (existT2 P Q u1 u2 u3) v p q r.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 652}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_existT2_r {A : Type} {P Q : A -> Type} {u : { a : A & P a & Q a }} {v1 : A} {v2 : P v1} {v3 : Q v1} (p : u.1 = v1) (q : rew p in u.2 = v2) (r : rew p in u.3 = v3) : u = existT2 P Q v1 v2 v3 := eq_sigT2 u (existT2 P Q v1 v2 v3) p q r.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 655}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sigT2_hprop {A P Q} (Q_hprop : forall (x : A) (p q : Q x), p = q) (u v : { a : A & P a & Q a }) (p : u = v :> { a : A & P a }) : u = v := eq_sigT2 u v (projT1_eq p) (projT2_eq p) (Q_hprop _ _ _).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 660}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sigT2_uncurried_iff {A P Q} (u v : { a : A & P a & Q a }) : u = v <-> { p : u.1 = v.1 & rew p in u.2 = v.2 & rew p in u.3 = v.3 }.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 669}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sigT2_rect {A P Q} {u v : { a : A & P a & Q a }} (R : u = v -> Type) (f : forall p q r, R (eq_sigT2 u v p q r)) : forall p, R p.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 679}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sigT2_rec {A P Q u v} (R : u = v :> { a : A & P a & Q a } -> Set) := eq_sigT2_rect R.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 687}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sigT2_ind {A P Q u v} (R : u = v :> { a : A & P a & Q a } -> Prop) := eq_sigT2_rec R.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 688}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sigT2_rect_existT2_l {A P Q} {u1 u2 u3 v} (R : _ -> Type) (f : forall p q r, R (@eq_existT2_l A P Q u1 u2 u3 v p q r)) : forall p, R p := eq_sigT2_rect R f.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 693}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sigT2_rect_existT2_r {A P Q} {u v1 v2 v3} (R : _ -> Type) (f : forall p q r, R (@eq_existT2_r A P Q u v1 v2 v3 p q r)) : forall p, R p := eq_sigT2_rect R f.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 697}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sigT2_rect_existT2 {A P Q} {u1 u2 u3 v1 v2 v3} (R : _ -> Type) (f : forall p q r, R (@eq_existT2_curried A P Q u1 v1 u2 v2 u3 v3 p q r)) : forall p, R p := eq_sigT2_rect R f.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 701}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sigT2_rect_uncurried {A P Q} {u v : { a : A & P a & Q a }} (R : u = v -> Type) (f : forall pqr : exists2 p : u.1 = v.1, _ & _, R (eq_sigT2 u v (ex_proj1 pqr) (ex_proj2 pqr) (ex_proj3 pqr))) : forall p, R p := eq_sigT2_rect R (fun p q r => f (ex_intro2 _ _ p q r)).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 710}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sigT2_rec_uncurried {A P Q u v} (R : u = v :> { a : A & P a & Q a } -> Set) := eq_sigT2_rect_uncurried R.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 714}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sigT2_ind_uncurried {A P Q u v} (R : u = v :> { a : A & P a & Q a } -> Prop) := eq_sigT2_rec_uncurried R.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 715}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sigT2_hprop_iff {A P Q} (Q_hprop : forall (x : A) (p q : Q x), p = q) (u v : { a : A & P a & Q a }) : u = v <-> (u = v :> { a : A & P a }) := conj (fun p => f_equal (@sigT_of_sigT2 _ _ _) p) (eq_sigT2_hprop Q_hprop u v).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 718}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sigT2_nondep {A B C : Type} (u v : { a : A & B & C }) (p : u.1 = v.1) (q : u.2 = v.2) (r : u.3 = v.3) : u = v := @eq_sigT2 _ _ _ u v p (eq_trans (rew_const _ _) q) (eq_trans (rew_const _ _) r).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 724}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma rew_sigT2 {A x} {P : A -> Type} (Q R : forall a, P a -> Prop) (u : { p : P x & Q x p & R x p }) {y} (H : x = y) : rew [fun a => { p : P a & Q a p & R a p }] H in u = existT2 (Q y) (R y) (rew H in u.1) (rew dependent H in u.2) (rew dependent H in u.3).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 730}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition sig_of_sig2_eq {A} {P Q : A -> Prop} {u v : { a : A | P a & Q a }} (p : u = v) : u = v :> { a : A | P a } := f_equal _ p.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 753}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition proj1_sig_of_sig2_eq {A} {P Q : A -> Prop} {u v : { a : A | P a & Q a }} (p : u = v) : proj1_sig u = proj1_sig v := proj1_sig_eq (sig_of_sig2_eq p).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 756}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition proj2_sig_of_sig2_eq {A} {P Q : A -> Prop} {u v : { a : A | P a & Q a }} (p : u = v) : rew proj1_sig_of_sig2_eq p in proj2_sig u = proj2_sig v := rew dependent p in eq_refl.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 761}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition proj3_sig_eq {A} {P Q : A -> Prop} {u v : { a : A | P a & Q a }} (p : u = v) : rew proj1_sig_of_sig2_eq p in proj3_sig u = proj3_sig v := rew dependent p in eq_refl.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 766}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_exist2_uncurried {A} {P Q : A -> Prop} {u1 v1 : A} {u2 : P u1} {v2 : P v1} {u3 : Q u1} {v3 : Q v1} (pqr : { p : u1 = v1 | rew p in u2 = v2 & rew p in u3 = v3 }) : exist2 _ _ u1 u2 u3 = exist2 _ _ v1 v2 v3.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 771}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sig2_uncurried {A} {P Q : A -> Prop} (u v : { a : A | P a & Q a }) (pqr : { p : proj1_sig u = proj1_sig v | rew p in proj2_sig u = proj2_sig v & rew p in proj3_sig u = proj3_sig v }) : u = v.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 783}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma eq_exist2_curried {A : Type} {P Q : A -> Prop} {u1 v1 : A} {u2 : P u1} {v2 : P v1} {u3 : Q u1} {v3 : Q v1} (p : u1 = v1) (q : rew p in u2 = v2) (r : rew p in u3 = v3) : exist2 P Q u1 u2 u3 = exist2 P Q v1 v2 v3.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 792}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sig2 {A} {P Q : A -> Prop} (u v : { a : A | P a & Q a }) (p : proj1_sig u = proj1_sig v) (q : rew p in proj2_sig u = proj2_sig v) (r : rew p in proj3_sig u = proj3_sig v) : u = v := eq_sig2_uncurried u v (exist2 _ _ p q r).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 799}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_exist2_l {A : Type} {P Q : A -> Prop} {u1 : A} {u2 : P u1} {u3 : Q u1} {v : { a : A | P a & Q a }} (p : u1 = proj1_sig v) (q : rew p in u2 = proj2_sig v) (r : rew p in u3 = proj3_sig v) : exist2 P Q u1 u2 u3 = v := eq_sig2 (exist2 P Q u1 u2 u3) v p q r.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 809}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_exist2_r {A : Type} {P Q : A -> Prop} {u : { a : A | P a & Q a }} {v1 : A} {v2 : P v1} {v3 : Q v1} (p : proj1_sig u = v1) (q : rew p in proj2_sig u = v2) (r : rew p in proj3_sig u = v3) : u = exist2 P Q v1 v2 v3 := eq_sig2 u (exist2 P Q v1 v2 v3) p q r.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 812}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sig2_hprop {A} {P Q : A -> Prop} (Q_hprop : forall (x : A) (p q : Q x), p = q) (u v : { a : A | P a & Q a }) (p : u = v :> { a : A | P a }) : u = v := eq_sig2 u v (proj1_sig_eq p) (proj2_sig_eq p) (Q_hprop _ _ _).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 817}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sig2_uncurried_iff {A P Q} (u v : { a : A | P a & Q a }) : u = v <-> { p : proj1_sig u = proj1_sig v | rew p in proj2_sig u = proj2_sig v & rew p in proj3_sig u = proj3_sig v }.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 826}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sig2_rect {A P Q} {u v : { a : A | P a & Q a }} (R : u = v -> Type) (f : forall p q r, R (eq_sig2 u v p q r)) : forall p, R p.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 836}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sig2_rec {A P Q u v} (R : u = v :> { a : A | P a & Q a } -> Set) := eq_sig2_rect R.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 844}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sig2_ind {A P Q u v} (R : u = v :> { a : A | P a & Q a } -> Prop) := eq_sig2_rec R.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 845}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sig2_rect_exist2_l {A P Q} {u1 u2 u3 v} (R : _ -> Type) (f : forall p q r, R (@eq_exist2_l A P Q u1 u2 u3 v p q r)) : forall p, R p := eq_sig2_rect R f.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 850}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sig2_rect_exist2_r {A P Q} {u v1 v2 v3} (R : _ -> Type) (f : forall p q r, R (@eq_exist2_r A P Q u v1 v2 v3 p q r)) : forall p, R p := eq_sig2_rect R f.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 854}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sig2_rect_exist2 {A P Q} {u1 u2 u3 v1 v2 v3} (R : _ -> Type) (f : forall p q r, R (@eq_exist2_curried A P Q u1 v1 u2 v2 u3 v3 p q r)) : forall p, R p := eq_sig2_rect R f.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 858}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sig2_rect_uncurried {A P Q} {u v : { a : A | P a & Q a }} (R : u = v -> Type) (f : forall pqr : exists2 p : proj1_sig u = proj1_sig v, _ & _, R (eq_sig2 u v (ex_proj1 pqr) (ex_proj2 pqr) (ex_proj3 pqr))) : forall p, R p := eq_sig2_rect R (fun p q r => f (ex_intro2 _ _ p q r)).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 867}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sig2_rec_uncurried {A P Q u v} (R : u = v :> { a : A | P a & Q a } -> Set) := eq_sig2_rect_uncurried R.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 871}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sig2_ind_uncurried {A P Q u v} (R : u = v :> { a : A | P a & Q a } -> Prop) := eq_sig2_rec_uncurried R.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 872}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sig2_hprop_iff {A} {P Q : A -> Prop} (Q_hprop : forall (x : A) (p q : Q x), p = q) (u v : { a : A | P a & Q a }) : u = v <-> (u = v :> { a : A | P a }) := conj (fun p => f_equal (@sig_of_sig2 _ _ _) p) (eq_sig2_hprop Q_hprop u v).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 875}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_sig2_nondep {A} {B C : Prop} (u v : @sig2 A (fun _ => B) (fun _ => C)) (p : proj1_sig u = proj1_sig v) (q : proj2_sig u = proj2_sig v) (r : proj3_sig u = proj3_sig v) : u = v := @eq_sig2 _ _ _ u v p (eq_trans (rew_const _ _) q) (eq_trans (rew_const _ _) r).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 881}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma rew_sig2 {A x} {P : A -> Type} (Q R : forall a, P a -> Prop) (u : { p : P x | Q x p & R x p }) {y} (H : x = y) : rew [fun a => { p : P a | Q a p & R a p }] H in u = exist2 (Q y) (R y) (rew H in proj1_sig u) (rew dependent H in proj2_sig u) (rew dependent H in proj3_sig u).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 887}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"Inductive sumbool (A B:Prop) : Set := | left : A -> {A} + {B} | right : B -> {A} + {B} where \\\"{ A } + { B }\\\" := (sumbool A B) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 907}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Inductive sumbool (A B:Prop) : Set := | left : A -> {A} + {B} | right : B -> {A} + {B} where \\\"{ A } + { B }\\\" := (sumbool A B) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 907}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"#[universes(template)] Inductive sumor (A:Type) (B:Prop) : Type := | inleft : A -> A + {B} | inright : B -> A + {B} where \\\"A + { B }\\\" := (sumor A B) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 922}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"#[universes(template)] Inductive sumor (A:Type) (B:Prop) : Type := | inleft : A -> A + {B} | inright : B -> A + {B} where \\\"A + { B }\\\" := (sumor A B) : type_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 922}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma Choice : (forall x:S, {y:S' | R x y}) -> {f:S -> S' | forall z:S, R z (f z)}.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 944}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma Choice2 : (forall x:S, {y:S' & R' x y}) -> {f:S -> S' & forall z:S, R' z (f z)}.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 952}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma bool_choice : (forall x:S, {R1 x} + {R2 x}) -> {f:S -> bool | forall x:S, f x = true /\\\\ R1 x \\\\/ f x = false /\\\\ R2 x}.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 960}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma dependent_choice : (forall x:X, {y | R x y}) -> forall x0, {f : nat -> X | f O = x0 /\\\\ forall n, R (f n) (f (S n))}.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 976}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition Exc := option A.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 1000}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition value := @Some A.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 1001}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition error := @None A.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 1002}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition except := False_rec.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 1006}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem absurd_set : forall (A:Prop) (C:Set), A -> ~ A -> C.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Specif.v\", \"module\": [], \"line\": 1010}",
    "{\"type\": \"TermType.VARIANT\", \"text\": \"Variant uint := UIntDecimal (u:Decimal.uint) | UIntHexadecimal (u:Hexadecimal.uint).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Number.v\", \"module\": [], \"line\": 14}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"Inductive uint := | Nil | D0 (_:uint) | D1 (_:uint) | D2 (_:uint) | D3 (_:uint) | D4 (_:uint) | D5 (_:uint) | D6 (_:uint) | D7 (_:uint) | D8 (_:uint) | D9 (_:uint).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Decimal.v\", \"module\": [], \"line\": 23}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"Inductive uint := | Nil | D0 (_:uint) | D1 (_:uint) | D2 (_:uint) | D3 (_:uint) | D4 (_:uint) | D5 (_:uint) | D6 (_:uint) | D7 (_:uint) | D8 (_:uint) | D9 (_:uint) | Da (_:uint) | Db (_:uint) | Dc (_:uint) | Dd (_:uint) | De (_:uint) | Df (_:uint).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Hexadecimal.v\", \"module\": [], \"line\": 23}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition zero := 0.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 30}",
    "{\"type\": \"TermType.VARIANT\", \"text\": \"Variant signed_int := IntDecimal (i:Decimal.int) | IntHexadecimal (i:Hexadecimal.int).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Number.v\", \"module\": [], \"line\": 16}",
    "{\"type\": \"TermType.VARIANT\", \"text\": \"Variant signed_int := Pos (d:uint) | Neg (d:uint).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Decimal.v\", \"module\": [], \"line\": 44}",
    "{\"type\": \"TermType.VARIANT\", \"text\": \"Variant signed_int := Pos (d:uint) | Neg (d:uint).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Hexadecimal.v\", \"module\": [], \"line\": 50}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation int := signed_int.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Number.v\", \"module\": [], \"line\": 17}",
    "{\"type\": \"TermType.VARIANT\", \"text\": \"Variant decimal := | Decimal (i:int) (f:uint) | DecimalExp (i:int) (f:uint) (e:int).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Decimal.v\", \"module\": [], \"line\": 52}",
    "{\"type\": \"TermType.VARIANT\", \"text\": \"Variant number := Decimal (d:Decimal.decimal) | Hexadecimal (h:Hexadecimal.hexadecimal).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Number.v\", \"module\": [], \"line\": 19}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation int_eq_dec := signed_int_eq_dec.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Number.v\", \"module\": [], \"line\": 24}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation int_beq := signed_int_beq.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Number.v\", \"module\": [], \"line\": 25}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation internal_int_dec_lb := internal_signed_int_dec_lb.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Number.v\", \"module\": [], \"line\": 26}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation internal_int_dec_bl := internal_signed_int_dec_bl.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Number.v\", \"module\": [], \"line\": 27}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint nb_digits d := match d with | Nil => O | D0 d | D1 d | D2 d | D3 d | D4 d | D5 d | D6 d | D7 d | D8 d | D9 d | Da d | Db d | Dc d | Dd d | De d | Df d => S (nb_digits d) end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Hexadecimal.v\", \"module\": [], \"line\": 82}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint nb_digits d := match d with | Nil => O | D0 d | D1 d | D2 d | D3 d | D4 d | D5 d | D6 d | D7 d | D8 d | D9 d => S (nb_digits d) end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Decimal.v\", \"module\": [], \"line\": 76}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint nzhead d := match d with | D0 d => nzhead d | _ => d end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Hexadecimal.v\", \"module\": [], \"line\": 97}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint nzhead d := match d with | D0 d => nzhead d | _ => d end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Decimal.v\", \"module\": [], \"line\": 90}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition unorm d := match nzhead d with | Nil => zero | d => d end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Hexadecimal.v\", \"module\": [], \"line\": 105}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition unorm d := match nzhead d with | Nil => zero | d => d end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Decimal.v\", \"module\": [], \"line\": 98}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition norm d := match d with | Pos d => Pos (unorm d) | Neg d => match nzhead d with | Nil => Pos zero | d => Neg d end end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Hexadecimal.v\", \"module\": [], \"line\": 113}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition norm d := match d with | Pos d => Pos (unorm d) | Neg d => match nzhead d with | Nil => Pos zero | d => Neg d end end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Decimal.v\", \"module\": [], \"line\": 106}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition opp (d:int) := match d with | Pos d => Neg d | Neg d => Pos d end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Hexadecimal.v\", \"module\": [], \"line\": 126}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition opp (d:int) := match d with | Pos d => Neg d | Neg d => Pos d end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Decimal.v\", \"module\": [], \"line\": 119}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition abs (d:int) : uint := match d with | Pos d => d | Neg d => d end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Hexadecimal.v\", \"module\": [], \"line\": 132}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition abs (d:int) : uint := match d with | Pos d => d | Neg d => d end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Decimal.v\", \"module\": [], \"line\": 125}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint revapp (d d' : uint) := match d with | Nil => d' | D0 d => revapp d (D0 d') | D1 d => revapp d (D1 d') | D2 d => revapp d (D2 d') | D3 d => revapp d (D3 d') | D4 d => revapp d (D4 d') | D5 d => revapp d (D5 d') | D6 d => revapp d (D6 d') | D7 d => revapp d (D7 d') | D8 d => revapp d (D8 d') | D9 d => revapp d (D9 d') | Da d => revapp d (Da d') | Db d => revapp d (Db d') | Dc d => revapp d (Dc d') | Dd d => revapp d (Dd d') | De d => revapp d (De d') | Df d => revapp d (Df d') end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Hexadecimal.v\", \"module\": [], \"line\": 141}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint revapp (d d' : uint) := match d with | Nil => d' | D0 d => revapp d (D0 d') | D1 d => revapp d (D1 d') | D2 d => revapp d (D2 d') | D3 d => revapp d (D3 d') | D4 d => revapp d (D4 d') | D5 d => revapp d (D5 d') | D6 d => revapp d (D6 d') | D7 d => revapp d (D7 d') | D8 d => revapp d (D8 d') | D9 d => revapp d (D9 d') end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Decimal.v\", \"module\": [], \"line\": 134}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition rev d := revapp d Nil.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Hexadecimal.v\", \"module\": [], \"line\": 162}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition rev d := revapp d Nil.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Decimal.v\", \"module\": [], \"line\": 149}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition app d d' := revapp (rev d) d'.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Decimal.v\", \"module\": [], \"line\": 151}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition app_int d1 d2 := match d1 with Pos d1 => Pos (app d1 d2) | Neg d1 => Neg (app d1 d2) end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Hexadecimal.v\", \"module\": [], \"line\": 166}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition app_int d1 d2 := match d1 with Pos d1 => Pos (app d1 d2) | Neg d1 => Neg (app d1 d2) end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Decimal.v\", \"module\": [], \"line\": 153}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition nztail d := let fix aux d_rev := match d_rev with | D0 d_rev => let (r, n) := aux d_rev in pair r (S n) | _ => pair d_rev O end in let (r, n) := aux (rev d) in pair (rev r) n.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Hexadecimal.v\", \"module\": [], \"line\": 172}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition nztail d := let fix aux d_rev := match d_rev with | D0 d_rev => let (r, n) := aux d_rev in pair r (S n) | _ => pair d_rev O end in let (r, n) := aux (rev d) in pair (rev r) n.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Decimal.v\", \"module\": [], \"line\": 159}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition nztail_int d := match d with | Pos d => let (r, n) := nztail d in pair (Pos r) n | Neg d => let (r, n) := nztail d in pair (Neg r) n end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Hexadecimal.v\", \"module\": [], \"line\": 180}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition nztail_int d := match d with | Pos d => let (r, n) := nztail d in pair (Pos r) n | Neg d => let (r, n) := nztail d in pair (Neg r) n end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Decimal.v\", \"module\": [], \"line\": 167}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint del_head n d := match n with | O => d | S n => match d with | Nil => zero | D0 d | D1 d | D2 d | D3 d | D4 d | D5 d | D6 d | D7 d | D8 d | D9 d | Da d | Db d | Dc d | Dd d | De d | Df d => del_head n d end end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Hexadecimal.v\", \"module\": [], \"line\": 189}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint del_head n d := match n with | O => d | S n => match d with | Nil => zero | D0 d | D1 d | D2 d | D3 d | D4 d | D5 d | D6 d | D7 d | D8 d | D9 d => del_head n d end end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Decimal.v\", \"module\": [], \"line\": 176}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition del_head_int n d := match d with | Pos d => del_head n d | Neg d => del_head n d end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Hexadecimal.v\", \"module\": [], \"line\": 201}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition del_head_int n d := match d with | Pos d => del_head n d | Neg d => del_head n d end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Decimal.v\", \"module\": [], \"line\": 187}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition del_tail n d := rev (del_head n (rev d)).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Hexadecimal.v\", \"module\": [], \"line\": 210}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition del_tail n d := rev (del_head n (rev d)).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Decimal.v\", \"module\": [], \"line\": 196}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition del_tail_int n d := match d with | Pos d => Pos (del_tail n d) | Neg d => Neg (del_tail n d) end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Hexadecimal.v\", \"module\": [], \"line\": 212}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition del_tail_int n d := match d with | Pos d => Pos (del_tail n d) | Neg d => Neg (del_tail n d) end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Decimal.v\", \"module\": [], \"line\": 198}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint succ d := match d with | Nil => D1 Nil | D0 d => D1 d | D1 d => D2 d | D2 d => D3 d | D3 d => D4 d | D4 d => D5 d | D5 d => D6 d | D6 d => D7 d | D7 d => D8 d | D8 d => D9 d | D9 d => Da d | Da d => Db d | Db d => Dc d | Dc d => Dd d | Dd d => De d | De d => Df d | Df d => D0 (succ d) end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Hexadecimal.v\", \"module\": [\"Little\"], \"line\": 222}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint succ d := match d with | Nil => D1 Nil | D0 d => D1 d | D1 d => D2 d | D2 d => D3 d | D3 d => D4 d | D4 d => D5 d | D5 d => D6 d | D6 d => D7 d | D7 d => D8 d | D8 d => D9 d | D9 d => D0 (succ d) end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Decimal.v\", \"module\": [\"Little\"], \"line\": 208}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint double d := match d with | Nil => Nil | D0 d => D0 (double d) | D1 d => D2 (double d) | D2 d => D4 (double d) | D3 d => D6 (double d) | D4 d => D8 (double d) | D5 d => Da (double d) | D6 d => Dc (double d) | D7 d => De (double d) | D8 d => D0 (succ_double d) | D9 d => D2 (succ_double d) | Da d => D4 (succ_double d) | Db d => D6 (succ_double d) | Dc d => D8 (succ_double d) | Dd d => Da (succ_double d) | De d => Dc (succ_double d) | Df d => De (succ_double d) end with succ_double d := match d with | Nil => D1 Nil | D0 d => D1 (double d) | D1 d => D3 (double d) | D2 d => D5 (double d) | D3 d => D7 (double d) | D4 d => D9 (double d) | D5 d => Db (double d) | D6 d => Dd (double d) | D7 d => Df (double d) | D8 d => D1 (succ_double d) | D9 d => D3 (succ_double d) | Da d => D5 (succ_double d) | Db d => D7 (succ_double d) | Dc d => D9 (succ_double d) | Dd d => Db (succ_double d) | De d => Dd (succ_double d) | Df d => Df (succ_double d) end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Hexadecimal.v\", \"module\": [\"Little\"], \"line\": 245}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint double d := match d with | Nil => Nil | D0 d => D0 (double d) | D1 d => D2 (double d) | D2 d => D4 (double d) | D3 d => D6 (double d) | D4 d => D8 (double d) | D5 d => D0 (succ_double d) | D6 d => D2 (succ_double d) | D7 d => D4 (succ_double d) | D8 d => D6 (succ_double d) | D9 d => D8 (succ_double d) end with succ_double d := match d with | Nil => D1 Nil | D0 d => D1 (double d) | D1 d => D3 (double d) | D2 d => D5 (double d) | D3 d => D7 (double d) | D4 d => D9 (double d) | D5 d => D1 (succ_double d) | D6 d => D3 (succ_double d) | D7 d => D5 (succ_double d) | D8 d => D7 (succ_double d) | D9 d => D9 (succ_double d) end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Decimal.v\", \"module\": [\"Little\"], \"line\": 225}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition uint_of_uint (i:uint) := i.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Number.v\", \"module\": [], \"line\": 36}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition uint_of_uint (i:uint) := i.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Decimal.v\", \"module\": [], \"line\": 260}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition int_of_int (i:int) := i.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Number.v\", \"module\": [], \"line\": 37}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition int_of_int (i:int) := i.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Decimal.v\", \"module\": [], \"line\": 261}",
    "{\"type\": \"TermType.VARIANT\", \"text\": \"Variant hexadecimal := | Hexadecimal (i:int) (f:uint) | HexadecimalExp (i:int) (f:uint) (e:Decimal.int).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Hexadecimal.v\", \"module\": [], \"line\": 58}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition t := nat.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 22}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition one := 1.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 31}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition two := 2.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 32}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition succ := S.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 36}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation pred := Nat.pred (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 44}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition pred n := match n with | 0 => n | S u => u end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 38}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint add n m := match n with | 0 => m | S p => S (p + m) end where \\\"n + m\\\" := (add n m) : nat_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 46}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Fixpoint add n m := match n with | 0 => m | S p => S (p + m) end where \\\"n + m\\\" := (add n m) : nat_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 46}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition double n := n + n.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 56}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint mul n m := match n with | 0 => 0 | S p => m + p * m end where \\\"n * m\\\" := (mul n m) : nat_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 58}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Fixpoint mul n m := match n with | 0 => 0 | S p => m + p * m end where \\\"n * m\\\" := (mul n m) : nat_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 58}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint sub n m := match n, m with | S k, S l => k - l | _, _ => n end where \\\"n - m\\\" := (sub n m) : nat_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 70}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Fixpoint sub n m := match n, m with | S k, S l => k - l | _, _ => n end where \\\"n - m\\\" := (sub n m) : nat_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 70}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint eqb n m : bool := match n, m with | 0, 0 => true | 0, S _ => false | S _, 0 => false | S n', S m' => eqb n' m' end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 82}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint leb n m : bool := match n, m with | 0, _ => true | _, 0 => false | S n', S m' => leb n' m' end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 90}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition ltb n m := leb (S n) m.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 97}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Infix \\\"=?\\\" := eqb (at level 70) : nat_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 99}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Infix \\\"<=?\\\" := leb (at level 70) : nat_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 100}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Infix \\\"<?\\\" := ltb (at level 70) : nat_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 101}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint compare n m : comparison := match n, m with | 0, 0 => Eq | 0, S _ => Lt | S _, 0 => Gt | S n', S m' => compare n' m' end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 103}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Infix \\\"?=\\\" := compare (at level 70) : nat_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 111}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation max := Nat.max (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 251}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint max n m := match n, m with | 0, _ => m | S n', 0 => n | S n', S m' => S (max n' m') end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 115}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation min := Nat.min (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 252}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint min n m := match n, m with | 0, _ => 0 | S n', 0 => 0 | S n', S m' => S (min n' m') end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 122}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint even n : bool := match n with | 0 => true | 1 => false | S (S n') => even n' end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 131}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition odd n := negb (even n).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 138}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint pow n m := match m with | 0 => 1 | S m => n * (n^m) end where \\\"n ^ m\\\" := (pow n m) : nat_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 142}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Fixpoint pow n m := match m with | 0 => 1 | S m => n * (n^m) end where \\\"n ^ m\\\" := (pow n m) : nat_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 142}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint tail_add n m := match n with | O => m | S n => tail_add n (S m) end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 152}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint tail_addmul r n m := match n with | O => r | S n => tail_addmul (tail_add m r) n m end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 160}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition tail_mul n m := tail_addmul 0 n m.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 166}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint of_uint_acc (d:Decimal.uint)(acc:nat) := match d with | Decimal.Nil => acc | Decimal.D0 d => of_uint_acc d (tail_mul ten acc) | Decimal.D1 d => of_uint_acc d (S (tail_mul ten acc)) | Decimal.D2 d => of_uint_acc d (S (S (tail_mul ten acc))) | Decimal.D3 d => of_uint_acc d (S (S (S (tail_mul ten acc)))) | Decimal.D4 d => of_uint_acc d (S (S (S (S (tail_mul ten acc))))) | Decimal.D5 d => of_uint_acc d (S (S (S (S (S (tail_mul ten acc)))))) | Decimal.D6 d => of_uint_acc d (S (S (S (S (S (S (tail_mul ten acc))))))) | Decimal.D7 d => of_uint_acc d (S (S (S (S (S (S (S (tail_mul ten acc)))))))) | Decimal.D8 d => of_uint_acc d (S (S (S (S (S (S (S (S (tail_mul ten acc))))))))) | Decimal.D9 d => of_uint_acc d (S (S (S (S (S (S (S (S (S (tail_mul ten acc)))))))))) end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 172}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition of_uint (d:Decimal.uint) := of_uint_acc d O.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 187}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint of_hex_uint_acc (d:Hexadecimal.uint)(acc:nat) := match d with | Hexadecimal.Nil => acc | Hexadecimal.D0 d => of_hex_uint_acc d (tail_mul sixteen acc) | Hexadecimal.D1 d => of_hex_uint_acc d (S (tail_mul sixteen acc)) | Hexadecimal.D2 d => of_hex_uint_acc d (S (S (tail_mul sixteen acc))) | Hexadecimal.D3 d => of_hex_uint_acc d (S (S (S (tail_mul sixteen acc)))) | Hexadecimal.D4 d => of_hex_uint_acc d (S (S (S (S (tail_mul sixteen acc))))) | Hexadecimal.D5 d => of_hex_uint_acc d (S (S (S (S (S (tail_mul sixteen acc)))))) | Hexadecimal.D6 d => of_hex_uint_acc d (S (S (S (S (S (S (tail_mul sixteen acc))))))) | Hexadecimal.D7 d => of_hex_uint_acc d (S (S (S (S (S (S (S (tail_mul sixteen acc)))))))) | Hexadecimal.D8 d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (tail_mul sixteen acc))))))))) | Hexadecimal.D9 d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (S (tail_mul sixteen acc)))))))))) | Hexadecimal.Da d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (S (S (tail_mul sixteen acc))))))))))) | Hexadecimal.Db d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (S (S (S (tail_mul sixteen acc)))))))))))) | Hexadecimal.Dc d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (S (S (S (S (tail_mul sixteen acc))))))))))))) | Hexadecimal.Dd d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (S (S (S (S (S (tail_mul sixteen acc)))))))))))))) | Hexadecimal.De d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (S (S (S (S (S (S (tail_mul sixteen acc))))))))))))))) | Hexadecimal.Df d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (tail_mul sixteen acc)))))))))))))))) end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 191}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition of_hex_uint (d:Hexadecimal.uint) := of_hex_uint_acc d O.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 212}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition of_num_uint (d:Number.uint) := match d with | Number.UIntDecimal d => of_uint d | Number.UIntHexadecimal d => of_hex_uint d end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 214}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint to_little_uint n acc := match n with | O => acc | S n => to_little_uint n (Decimal.Little.succ acc) end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 220}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition to_uint n := Decimal.rev (to_little_uint n Decimal.zero).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 226}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint to_little_hex_uint n acc := match n with | O => acc | S n => to_little_hex_uint n (Hexadecimal.Little.succ acc) end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 229}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition to_hex_uint n := Hexadecimal.rev (to_little_hex_uint n Hexadecimal.zero).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 235}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition to_num_uint n := Number.UIntDecimal (to_uint n).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 238}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition to_num_hex_uint n := Number.UIntHexadecimal (to_hex_uint n).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 240}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition of_int (d:Decimal.int) : option nat := match Decimal.norm d with | Decimal.Pos u => Some (of_uint u) | _ => None end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 242}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition of_hex_int (d:Hexadecimal.int) : option nat := match Hexadecimal.norm d with | Hexadecimal.Pos u => Some (of_hex_uint u) | _ => None end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 248}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition of_num_int (d:Number.int) : option nat := match d with | Number.IntDecimal d => of_int d | Number.IntHexadecimal d => of_hex_int d end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 254}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition to_int n := Decimal.Pos (to_uint n).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 260}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition to_hex_int n := Hexadecimal.Pos (to_hex_uint n).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 262}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition to_num_int n := Number.IntDecimal (to_int n).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 264}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint divmod x y q u := match x with | 0 => (q,u) | S x' => match u with | 0 => divmod x' y (S q) y | S u' => divmod x' y q u' end end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 273}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition div x y := match y with | 0 => y | S y' => fst (divmod x y' 0 y') end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 282}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition modulo x y := match y with | 0 => x | S y' => y' - snd (divmod x y' 0 y') end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 288}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Infix \\\"/\\\" := div : nat_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 294}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Infix \\\"mod\\\" := modulo (at level 40, no associativity) : nat_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 295}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint gcd a b := match a with | O => b | S a' => gcd (b mod (S a')) (S a') end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 305}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition square n := n * n.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 313}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint sqrt_iter k p q r := match k with | O => p | S k' => match r with | O => sqrt_iter k' (S p) (S (S q)) (S (S q)) | S r' => sqrt_iter k' p q r' end end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 330}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition sqrt n := sqrt_iter n 0 0 0.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 339}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint log2_iter k p q r := match k with | O => p | S k' => match r with | O => log2_iter k' (S p) (S q) q | S r' => log2_iter k' p (S q) r' end end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 374}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition log2 n := log2_iter (pred n) 0 1 0.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 383}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition iter (n:nat) {A} (f:A->A) (x:A) : A := nat_rect (fun _ => A) x (fun _ => f) n.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 387}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint div2 n := match n with | 0 => 0 | S 0 => 0 | S (S n') => S (div2 n') end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 399}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint testbit a n : bool := match n with | 0 => odd a | S n => testbit (div2 a) n end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 406}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition shiftl a := nat_rect _ a (fun _ => double).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 412}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition shiftr a := nat_rect _ a (fun _ => div2).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 413}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint bitwise (op:bool->bool->bool) n a b := match n with | 0 => 0 | S n' => (if op (odd a) (odd b) then 1 else 0) + 2*(bitwise op n' (div2 a) (div2 b)) end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 415}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition land a b := bitwise andb a a b.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 423}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition lor a b := bitwise orb (max a b) a b.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 424}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition ldiff a b := bitwise (fun b b' => andb b (negb b')) a a b.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 425}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition lxor a b := bitwise xorb (max a b) a b.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Nat.v\", \"module\": [], \"line\": 426}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"Inductive byte := | x00 | x01 | x02 | x03 | x04 | x05 | x06 | x07 | x08 | x09 | x0a | x0b | x0c | x0d | x0e | x0f | x10 | x11 | x12 | x13 | x14 | x15 | x16 | x17 | x18 | x19 | x1a | x1b | x1c | x1d | x1e | x1f | x20 | x21 | x22 | x23 | x24 | x25 | x26 | x27 | x28 | x29 | x2a | x2b | x2c | x2d | x2e | x2f | x30 | x31 | x32 | x33 | x34 | x35 | x36 | x37 | x38 | x39 | x3a | x3b | x3c | x3d | x3e | x3f | x40 | x41 | x42 | x43 | x44 | x45 | x46 | x47 | x48 | x49 | x4a | x4b | x4c | x4d | x4e | x4f | x50 | x51 | x52 | x53 | x54 | x55 | x56 | x57 | x58 | x59 | x5a | x5b | x5c | x5d | x5e | x5f | x60 | x61 | x62 | x63 | x64 | x65 | x66 | x67 | x68 | x69 | x6a | x6b | x6c | x6d | x6e | x6f | x70 | x71 | x72 | x73 | x74 | x75 | x76 | x77 | x78 | x79 | x7a | x7b | x7c | x7d | x7e | x7f | x80 | x81 | x82 | x83 | x84 | x85 | x86 | x87 | x88 | x89 | x8a | x8b | x8c | x8d | x8e | x8f | x90 | x91 | x92 | x93 | x94 | x95 | x96 | x97 | x98 | x99 | x9a | x9b | x9c | x9d | x9e | x9f | xa0 | xa1 | xa2 | xa3 | xa4 | xa5 | xa6 | xa7 | xa8 | xa9 | xaa | xab | xac | xad | xae | xaf | xb0 | xb1 | xb2 | xb3 | xb4 | xb5 | xb6 | xb7 | xb8 | xb9 | xba | xbb | xbc | xbd | xbe | xbf | xc0 | xc1 | xc2 | xc3 | xc4 | xc5 | xc6 | xc7 | xc8 | xc9 | xca | xcb | xcc | xcd | xce | xcf | xd0 | xd1 | xd2 | xd3 | xd4 | xd5 | xd6 | xd7 | xd8 | xd9 | xda | xdb | xdc | xdd | xde | xdf | xe0 | xe1 | xe2 | xe3 | xe4 | xe5 | xe6 | xe7 | xe8 | xe9 | xea | xeb | xec | xed | xee | xef | xf0 | xf1 | xf2 | xf3 | xf4 | xf5 | xf6 | xf7 | xf8 | xf9 | xfa | xfb | xfc | xfd | xfe | xff .\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Byte.v\", \"module\": [], \"line\": 27}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition of_bits (b : bool * (bool * (bool * (bool * (bool * (bool * (bool * bool))))))) : byte := match b with | (0,(0,(0,(0,(0,(0,(0,0))))))) => x00 | (1,(0,(0,(0,(0,(0,(0,0))))))) => x01 | (0,(1,(0,(0,(0,(0,(0,0))))))) => x02 | (1,(1,(0,(0,(0,(0,(0,0))))))) => x03 | (0,(0,(1,(0,(0,(0,(0,0))))))) => x04 | (1,(0,(1,(0,(0,(0,(0,0))))))) => x05 | (0,(1,(1,(0,(0,(0,(0,0))))))) => x06 | (1,(1,(1,(0,(0,(0,(0,0))))))) => x07 | (0,(0,(0,(1,(0,(0,(0,0))))))) => x08 | (1,(0,(0,(1,(0,(0,(0,0))))))) => x09 | (0,(1,(0,(1,(0,(0,(0,0))))))) => x0a | (1,(1,(0,(1,(0,(0,(0,0))))))) => x0b | (0,(0,(1,(1,(0,(0,(0,0))))))) => x0c | (1,(0,(1,(1,(0,(0,(0,0))))))) => x0d | (0,(1,(1,(1,(0,(0,(0,0))))))) => x0e | (1,(1,(1,(1,(0,(0,(0,0))))))) => x0f | (0,(0,(0,(0,(1,(0,(0,0))))))) => x10 | (1,(0,(0,(0,(1,(0,(0,0))))))) => x11 | (0,(1,(0,(0,(1,(0,(0,0))))))) => x12 | (1,(1,(0,(0,(1,(0,(0,0))))))) => x13 | (0,(0,(1,(0,(1,(0,(0,0))))))) => x14 | (1,(0,(1,(0,(1,(0,(0,0))))))) => x15 | (0,(1,(1,(0,(1,(0,(0,0))))))) => x16 | (1,(1,(1,(0,(1,(0,(0,0))))))) => x17 | (0,(0,(0,(1,(1,(0,(0,0))))))) => x18 | (1,(0,(0,(1,(1,(0,(0,0))))))) => x19 | (0,(1,(0,(1,(1,(0,(0,0))))))) => x1a | (1,(1,(0,(1,(1,(0,(0,0))))))) => x1b | (0,(0,(1,(1,(1,(0,(0,0))))))) => x1c | (1,(0,(1,(1,(1,(0,(0,0))))))) => x1d | (0,(1,(1,(1,(1,(0,(0,0))))))) => x1e | (1,(1,(1,(1,(1,(0,(0,0))))))) => x1f | (0,(0,(0,(0,(0,(1,(0,0))))))) => x20 | (1,(0,(0,(0,(0,(1,(0,0))))))) => x21 | (0,(1,(0,(0,(0,(1,(0,0))))))) => x22 | (1,(1,(0,(0,(0,(1,(0,0))))))) => x23 | (0,(0,(1,(0,(0,(1,(0,0))))))) => x24 | (1,(0,(1,(0,(0,(1,(0,0))))))) => x25 | (0,(1,(1,(0,(0,(1,(0,0))))))) => x26 | (1,(1,(1,(0,(0,(1,(0,0))))))) => x27 | (0,(0,(0,(1,(0,(1,(0,0))))))) => x28 | (1,(0,(0,(1,(0,(1,(0,0))))))) => x29 | (0,(1,(0,(1,(0,(1,(0,0))))))) => x2a | (1,(1,(0,(1,(0,(1,(0,0))))))) => x2b | (0,(0,(1,(1,(0,(1,(0,0))))))) => x2c | (1,(0,(1,(1,(0,(1,(0,0))))))) => x2d | (0,(1,(1,(1,(0,(1,(0,0))))))) => x2e | (1,(1,(1,(1,(0,(1,(0,0))))))) => x2f | (0,(0,(0,(0,(1,(1,(0,0))))))) => x30 | (1,(0,(0,(0,(1,(1,(0,0))))))) => x31 | (0,(1,(0,(0,(1,(1,(0,0))))))) => x32 | (1,(1,(0,(0,(1,(1,(0,0))))))) => x33 | (0,(0,(1,(0,(1,(1,(0,0))))))) => x34 | (1,(0,(1,(0,(1,(1,(0,0))))))) => x35 | (0,(1,(1,(0,(1,(1,(0,0))))))) => x36 | (1,(1,(1,(0,(1,(1,(0,0))))))) => x37 | (0,(0,(0,(1,(1,(1,(0,0))))))) => x38 | (1,(0,(0,(1,(1,(1,(0,0))))))) => x39 | (0,(1,(0,(1,(1,(1,(0,0))))))) => x3a | (1,(1,(0,(1,(1,(1,(0,0))))))) => x3b | (0,(0,(1,(1,(1,(1,(0,0))))))) => x3c | (1,(0,(1,(1,(1,(1,(0,0))))))) => x3d | (0,(1,(1,(1,(1,(1,(0,0))))))) => x3e | (1,(1,(1,(1,(1,(1,(0,0))))))) => x3f | (0,(0,(0,(0,(0,(0,(1,0))))))) => x40 | (1,(0,(0,(0,(0,(0,(1,0))))))) => x41 | (0,(1,(0,(0,(0,(0,(1,0))))))) => x42 | (1,(1,(0,(0,(0,(0,(1,0))))))) => x43 | (0,(0,(1,(0,(0,(0,(1,0))))))) => x44 | (1,(0,(1,(0,(0,(0,(1,0))))))) => x45 | (0,(1,(1,(0,(0,(0,(1,0))))))) => x46 | (1,(1,(1,(0,(0,(0,(1,0))))))) => x47 | (0,(0,(0,(1,(0,(0,(1,0))))))) => x48 | (1,(0,(0,(1,(0,(0,(1,0))))))) => x49 | (0,(1,(0,(1,(0,(0,(1,0))))))) => x4a | (1,(1,(0,(1,(0,(0,(1,0))))))) => x4b | (0,(0,(1,(1,(0,(0,(1,0))))))) => x4c | (1,(0,(1,(1,(0,(0,(1,0))))))) => x4d | (0,(1,(1,(1,(0,(0,(1,0))))))) => x4e | (1,(1,(1,(1,(0,(0,(1,0))))))) => x4f | (0,(0,(0,(0,(1,(0,(1,0))))))) => x50 | (1,(0,(0,(0,(1,(0,(1,0))))))) => x51 | (0,(1,(0,(0,(1,(0,(1,0))))))) => x52 | (1,(1,(0,(0,(1,(0,(1,0))))))) => x53 | (0,(0,(1,(0,(1,(0,(1,0))))))) => x54 | (1,(0,(1,(0,(1,(0,(1,0))))))) => x55 | (0,(1,(1,(0,(1,(0,(1,0))))))) => x56 | (1,(1,(1,(0,(1,(0,(1,0))))))) => x57 | (0,(0,(0,(1,(1,(0,(1,0))))))) => x58 | (1,(0,(0,(1,(1,(0,(1,0))))))) => x59 | (0,(1,(0,(1,(1,(0,(1,0))))))) => x5a | (1,(1,(0,(1,(1,(0,(1,0))))))) => x5b | (0,(0,(1,(1,(1,(0,(1,0))))))) => x5c | (1,(0,(1,(1,(1,(0,(1,0))))))) => x5d | (0,(1,(1,(1,(1,(0,(1,0))))))) => x5e | (1,(1,(1,(1,(1,(0,(1,0))))))) => x5f | (0,(0,(0,(0,(0,(1,(1,0))))))) => x60 | (1,(0,(0,(0,(0,(1,(1,0))))))) => x61 | (0,(1,(0,(0,(0,(1,(1,0))))))) => x62 | (1,(1,(0,(0,(0,(1,(1,0))))))) => x63 | (0,(0,(1,(0,(0,(1,(1,0))))))) => x64 | (1,(0,(1,(0,(0,(1,(1,0))))))) => x65 | (0,(1,(1,(0,(0,(1,(1,0))))))) => x66 | (1,(1,(1,(0,(0,(1,(1,0))))))) => x67 | (0,(0,(0,(1,(0,(1,(1,0))))))) => x68 | (1,(0,(0,(1,(0,(1,(1,0))))))) => x69 | (0,(1,(0,(1,(0,(1,(1,0))))))) => x6a | (1,(1,(0,(1,(0,(1,(1,0))))))) => x6b | (0,(0,(1,(1,(0,(1,(1,0))))))) => x6c | (1,(0,(1,(1,(0,(1,(1,0))))))) => x6d | (0,(1,(1,(1,(0,(1,(1,0))))))) => x6e | (1,(1,(1,(1,(0,(1,(1,0))))))) => x6f | (0,(0,(0,(0,(1,(1,(1,0))))))) => x70 | (1,(0,(0,(0,(1,(1,(1,0))))))) => x71 | (0,(1,(0,(0,(1,(1,(1,0))))))) => x72 | (1,(1,(0,(0,(1,(1,(1,0))))))) => x73 | (0,(0,(1,(0,(1,(1,(1,0))))))) => x74 | (1,(0,(1,(0,(1,(1,(1,0))))))) => x75 | (0,(1,(1,(0,(1,(1,(1,0))))))) => x76 | (1,(1,(1,(0,(1,(1,(1,0))))))) => x77 | (0,(0,(0,(1,(1,(1,(1,0))))))) => x78 | (1,(0,(0,(1,(1,(1,(1,0))))))) => x79 | (0,(1,(0,(1,(1,(1,(1,0))))))) => x7a | (1,(1,(0,(1,(1,(1,(1,0))))))) => x7b | (0,(0,(1,(1,(1,(1,(1,0))))))) => x7c | (1,(0,(1,(1,(1,(1,(1,0))))))) => x7d | (0,(1,(1,(1,(1,(1,(1,0))))))) => x7e | (1,(1,(1,(1,(1,(1,(1,0))))))) => x7f | (0,(0,(0,(0,(0,(0,(0,1))))))) => x80 | (1,(0,(0,(0,(0,(0,(0,1))))))) => x81 | (0,(1,(0,(0,(0,(0,(0,1))))))) => x82 | (1,(1,(0,(0,(0,(0,(0,1))))))) => x83 | (0,(0,(1,(0,(0,(0,(0,1))))))) => x84 | (1,(0,(1,(0,(0,(0,(0,1))))))) => x85 | (0,(1,(1,(0,(0,(0,(0,1))))))) => x86 | (1,(1,(1,(0,(0,(0,(0,1))))))) => x87 | (0,(0,(0,(1,(0,(0,(0,1))))))) => x88 | (1,(0,(0,(1,(0,(0,(0,1))))))) => x89 | (0,(1,(0,(1,(0,(0,(0,1))))))) => x8a | (1,(1,(0,(1,(0,(0,(0,1))))))) => x8b | (0,(0,(1,(1,(0,(0,(0,1))))))) => x8c | (1,(0,(1,(1,(0,(0,(0,1))))))) => x8d | (0,(1,(1,(1,(0,(0,(0,1))))))) => x8e | (1,(1,(1,(1,(0,(0,(0,1))))))) => x8f | (0,(0,(0,(0,(1,(0,(0,1))))))) => x90 | (1,(0,(0,(0,(1,(0,(0,1))))))) => x91 | (0,(1,(0,(0,(1,(0,(0,1))))))) => x92 | (1,(1,(0,(0,(1,(0,(0,1))))))) => x93 | (0,(0,(1,(0,(1,(0,(0,1))))))) => x94 | (1,(0,(1,(0,(1,(0,(0,1))))))) => x95 | (0,(1,(1,(0,(1,(0,(0,1))))))) => x96 | (1,(1,(1,(0,(1,(0,(0,1))))))) => x97 | (0,(0,(0,(1,(1,(0,(0,1))))))) => x98 | (1,(0,(0,(1,(1,(0,(0,1))))))) => x99 | (0,(1,(0,(1,(1,(0,(0,1))))))) => x9a | (1,(1,(0,(1,(1,(0,(0,1))))))) => x9b | (0,(0,(1,(1,(1,(0,(0,1))))))) => x9c | (1,(0,(1,(1,(1,(0,(0,1))))))) => x9d | (0,(1,(1,(1,(1,(0,(0,1))))))) => x9e | (1,(1,(1,(1,(1,(0,(0,1))))))) => x9f | (0,(0,(0,(0,(0,(1,(0,1))))))) => xa0 | (1,(0,(0,(0,(0,(1,(0,1))))))) => xa1 | (0,(1,(0,(0,(0,(1,(0,1))))))) => xa2 | (1,(1,(0,(0,(0,(1,(0,1))))))) => xa3 | (0,(0,(1,(0,(0,(1,(0,1))))))) => xa4 | (1,(0,(1,(0,(0,(1,(0,1))))))) => xa5 | (0,(1,(1,(0,(0,(1,(0,1))))))) => xa6 | (1,(1,(1,(0,(0,(1,(0,1))))))) => xa7 | (0,(0,(0,(1,(0,(1,(0,1))))))) => xa8 | (1,(0,(0,(1,(0,(1,(0,1))))))) => xa9 | (0,(1,(0,(1,(0,(1,(0,1))))))) => xaa | (1,(1,(0,(1,(0,(1,(0,1))))))) => xab | (0,(0,(1,(1,(0,(1,(0,1))))))) => xac | (1,(0,(1,(1,(0,(1,(0,1))))))) => xad | (0,(1,(1,(1,(0,(1,(0,1))))))) => xae | (1,(1,(1,(1,(0,(1,(0,1))))))) => xaf | (0,(0,(0,(0,(1,(1,(0,1))))))) => xb0 | (1,(0,(0,(0,(1,(1,(0,1))))))) => xb1 | (0,(1,(0,(0,(1,(1,(0,1))))))) => xb2 | (1,(1,(0,(0,(1,(1,(0,1))))))) => xb3 | (0,(0,(1,(0,(1,(1,(0,1))))))) => xb4 | (1,(0,(1,(0,(1,(1,(0,1))))))) => xb5 | (0,(1,(1,(0,(1,(1,(0,1))))))) => xb6 | (1,(1,(1,(0,(1,(1,(0,1))))))) => xb7 | (0,(0,(0,(1,(1,(1,(0,1))))))) => xb8 | (1,(0,(0,(1,(1,(1,(0,1))))))) => xb9 | (0,(1,(0,(1,(1,(1,(0,1))))))) => xba | (1,(1,(0,(1,(1,(1,(0,1))))))) => xbb | (0,(0,(1,(1,(1,(1,(0,1))))))) => xbc | (1,(0,(1,(1,(1,(1,(0,1))))))) => xbd | (0,(1,(1,(1,(1,(1,(0,1))))))) => xbe | (1,(1,(1,(1,(1,(1,(0,1))))))) => xbf | (0,(0,(0,(0,(0,(0,(1,1))))))) => xc0 | (1,(0,(0,(0,(0,(0,(1,1))))))) => xc1 | (0,(1,(0,(0,(0,(0,(1,1))))))) => xc2 | (1,(1,(0,(0,(0,(0,(1,1))))))) => xc3 | (0,(0,(1,(0,(0,(0,(1,1))))))) => xc4 | (1,(0,(1,(0,(0,(0,(1,1))))))) => xc5 | (0,(1,(1,(0,(0,(0,(1,1))))))) => xc6 | (1,(1,(1,(0,(0,(0,(1,1))))))) => xc7 | (0,(0,(0,(1,(0,(0,(1,1))))))) => xc8 | (1,(0,(0,(1,(0,(0,(1,1))))))) => xc9 | (0,(1,(0,(1,(0,(0,(1,1))))))) => xca | (1,(1,(0,(1,(0,(0,(1,1))))))) => xcb | (0,(0,(1,(1,(0,(0,(1,1))))))) => xcc | (1,(0,(1,(1,(0,(0,(1,1))))))) => xcd | (0,(1,(1,(1,(0,(0,(1,1))))))) => xce | (1,(1,(1,(1,(0,(0,(1,1))))))) => xcf | (0,(0,(0,(0,(1,(0,(1,1))))))) => xd0 | (1,(0,(0,(0,(1,(0,(1,1))))))) => xd1 | (0,(1,(0,(0,(1,(0,(1,1))))))) => xd2 | (1,(1,(0,(0,(1,(0,(1,1))))))) => xd3 | (0,(0,(1,(0,(1,(0,(1,1))))))) => xd4 | (1,(0,(1,(0,(1,(0,(1,1))))))) => xd5 | (0,(1,(1,(0,(1,(0,(1,1))))))) => xd6 | (1,(1,(1,(0,(1,(0,(1,1))))))) => xd7 | (0,(0,(0,(1,(1,(0,(1,1))))))) => xd8 | (1,(0,(0,(1,(1,(0,(1,1))))))) => xd9 | (0,(1,(0,(1,(1,(0,(1,1))))))) => xda | (1,(1,(0,(1,(1,(0,(1,1))))))) => xdb | (0,(0,(1,(1,(1,(0,(1,1))))))) => xdc | (1,(0,(1,(1,(1,(0,(1,1))))))) => xdd | (0,(1,(1,(1,(1,(0,(1,1))))))) => xde | (1,(1,(1,(1,(1,(0,(1,1))))))) => xdf | (0,(0,(0,(0,(0,(1,(1,1))))))) => xe0 | (1,(0,(0,(0,(0,(1,(1,1))))))) => xe1 | (0,(1,(0,(0,(0,(1,(1,1))))))) => xe2 | (1,(1,(0,(0,(0,(1,(1,1))))))) => xe3 | (0,(0,(1,(0,(0,(1,(1,1))))))) => xe4 | (1,(0,(1,(0,(0,(1,(1,1))))))) => xe5 | (0,(1,(1,(0,(0,(1,(1,1))))))) => xe6 | (1,(1,(1,(0,(0,(1,(1,1))))))) => xe7 | (0,(0,(0,(1,(0,(1,(1,1))))))) => xe8 | (1,(0,(0,(1,(0,(1,(1,1))))))) => xe9 | (0,(1,(0,(1,(0,(1,(1,1))))))) => xea | (1,(1,(0,(1,(0,(1,(1,1))))))) => xeb | (0,(0,(1,(1,(0,(1,(1,1))))))) => xec | (1,(0,(1,(1,(0,(1,(1,1))))))) => xed | (0,(1,(1,(1,(0,(1,(1,1))))))) => xee | (1,(1,(1,(1,(0,(1,(1,1))))))) => xef | (0,(0,(0,(0,(1,(1,(1,1))))))) => xf0 | (1,(0,(0,(0,(1,(1,(1,1))))))) => xf1 | (0,(1,(0,(0,(1,(1,(1,1))))))) => xf2 | (1,(1,(0,(0,(1,(1,(1,1))))))) => xf3 | (0,(0,(1,(0,(1,(1,(1,1))))))) => xf4 | (1,(0,(1,(0,(1,(1,(1,1))))))) => xf5 | (0,(1,(1,(0,(1,(1,(1,1))))))) => xf6 | (1,(1,(1,(0,(1,(1,(1,1))))))) => xf7 | (0,(0,(0,(1,(1,(1,(1,1))))))) => xf8 | (1,(0,(0,(1,(1,(1,(1,1))))))) => xf9 | (0,(1,(0,(1,(1,(1,(1,1))))))) => xfa | (1,(1,(0,(1,(1,(1,(1,1))))))) => xfb | (0,(0,(1,(1,(1,(1,(1,1))))))) => xfc | (1,(0,(1,(1,(1,(1,(1,1))))))) => xfd | (0,(1,(1,(1,(1,(1,(1,1))))))) => xfe | (1,(1,(1,(1,(1,(1,(1,1))))))) => xff end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Byte.v\", \"module\": [], \"line\": 294}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition to_bits (b : byte) : bool * (bool * (bool * (bool * (bool * (bool * (bool * bool)))))) := match b with | x00 => (0,(0,(0,(0,(0,(0,(0,0))))))) | x01 => (1,(0,(0,(0,(0,(0,(0,0))))))) | x02 => (0,(1,(0,(0,(0,(0,(0,0))))))) | x03 => (1,(1,(0,(0,(0,(0,(0,0))))))) | x04 => (0,(0,(1,(0,(0,(0,(0,0))))))) | x05 => (1,(0,(1,(0,(0,(0,(0,0))))))) | x06 => (0,(1,(1,(0,(0,(0,(0,0))))))) | x07 => (1,(1,(1,(0,(0,(0,(0,0))))))) | x08 => (0,(0,(0,(1,(0,(0,(0,0))))))) | x09 => (1,(0,(0,(1,(0,(0,(0,0))))))) | x0a => (0,(1,(0,(1,(0,(0,(0,0))))))) | x0b => (1,(1,(0,(1,(0,(0,(0,0))))))) | x0c => (0,(0,(1,(1,(0,(0,(0,0))))))) | x0d => (1,(0,(1,(1,(0,(0,(0,0))))))) | x0e => (0,(1,(1,(1,(0,(0,(0,0))))))) | x0f => (1,(1,(1,(1,(0,(0,(0,0))))))) | x10 => (0,(0,(0,(0,(1,(0,(0,0))))))) | x11 => (1,(0,(0,(0,(1,(0,(0,0))))))) | x12 => (0,(1,(0,(0,(1,(0,(0,0))))))) | x13 => (1,(1,(0,(0,(1,(0,(0,0))))))) | x14 => (0,(0,(1,(0,(1,(0,(0,0))))))) | x15 => (1,(0,(1,(0,(1,(0,(0,0))))))) | x16 => (0,(1,(1,(0,(1,(0,(0,0))))))) | x17 => (1,(1,(1,(0,(1,(0,(0,0))))))) | x18 => (0,(0,(0,(1,(1,(0,(0,0))))))) | x19 => (1,(0,(0,(1,(1,(0,(0,0))))))) | x1a => (0,(1,(0,(1,(1,(0,(0,0))))))) | x1b => (1,(1,(0,(1,(1,(0,(0,0))))))) | x1c => (0,(0,(1,(1,(1,(0,(0,0))))))) | x1d => (1,(0,(1,(1,(1,(0,(0,0))))))) | x1e => (0,(1,(1,(1,(1,(0,(0,0))))))) | x1f => (1,(1,(1,(1,(1,(0,(0,0))))))) | x20 => (0,(0,(0,(0,(0,(1,(0,0))))))) | x21 => (1,(0,(0,(0,(0,(1,(0,0))))))) | x22 => (0,(1,(0,(0,(0,(1,(0,0))))))) | x23 => (1,(1,(0,(0,(0,(1,(0,0))))))) | x24 => (0,(0,(1,(0,(0,(1,(0,0))))))) | x25 => (1,(0,(1,(0,(0,(1,(0,0))))))) | x26 => (0,(1,(1,(0,(0,(1,(0,0))))))) | x27 => (1,(1,(1,(0,(0,(1,(0,0))))))) | x28 => (0,(0,(0,(1,(0,(1,(0,0))))))) | x29 => (1,(0,(0,(1,(0,(1,(0,0))))))) | x2a => (0,(1,(0,(1,(0,(1,(0,0))))))) | x2b => (1,(1,(0,(1,(0,(1,(0,0))))))) | x2c => (0,(0,(1,(1,(0,(1,(0,0))))))) | x2d => (1,(0,(1,(1,(0,(1,(0,0))))))) | x2e => (0,(1,(1,(1,(0,(1,(0,0))))))) | x2f => (1,(1,(1,(1,(0,(1,(0,0))))))) | x30 => (0,(0,(0,(0,(1,(1,(0,0))))))) | x31 => (1,(0,(0,(0,(1,(1,(0,0))))))) | x32 => (0,(1,(0,(0,(1,(1,(0,0))))))) | x33 => (1,(1,(0,(0,(1,(1,(0,0))))))) | x34 => (0,(0,(1,(0,(1,(1,(0,0))))))) | x35 => (1,(0,(1,(0,(1,(1,(0,0))))))) | x36 => (0,(1,(1,(0,(1,(1,(0,0))))))) | x37 => (1,(1,(1,(0,(1,(1,(0,0))))))) | x38 => (0,(0,(0,(1,(1,(1,(0,0))))))) | x39 => (1,(0,(0,(1,(1,(1,(0,0))))))) | x3a => (0,(1,(0,(1,(1,(1,(0,0))))))) | x3b => (1,(1,(0,(1,(1,(1,(0,0))))))) | x3c => (0,(0,(1,(1,(1,(1,(0,0))))))) | x3d => (1,(0,(1,(1,(1,(1,(0,0))))))) | x3e => (0,(1,(1,(1,(1,(1,(0,0))))))) | x3f => (1,(1,(1,(1,(1,(1,(0,0))))))) | x40 => (0,(0,(0,(0,(0,(0,(1,0))))))) | x41 => (1,(0,(0,(0,(0,(0,(1,0))))))) | x42 => (0,(1,(0,(0,(0,(0,(1,0))))))) | x43 => (1,(1,(0,(0,(0,(0,(1,0))))))) | x44 => (0,(0,(1,(0,(0,(0,(1,0))))))) | x45 => (1,(0,(1,(0,(0,(0,(1,0))))))) | x46 => (0,(1,(1,(0,(0,(0,(1,0))))))) | x47 => (1,(1,(1,(0,(0,(0,(1,0))))))) | x48 => (0,(0,(0,(1,(0,(0,(1,0))))))) | x49 => (1,(0,(0,(1,(0,(0,(1,0))))))) | x4a => (0,(1,(0,(1,(0,(0,(1,0))))))) | x4b => (1,(1,(0,(1,(0,(0,(1,0))))))) | x4c => (0,(0,(1,(1,(0,(0,(1,0))))))) | x4d => (1,(0,(1,(1,(0,(0,(1,0))))))) | x4e => (0,(1,(1,(1,(0,(0,(1,0))))))) | x4f => (1,(1,(1,(1,(0,(0,(1,0))))))) | x50 => (0,(0,(0,(0,(1,(0,(1,0))))))) | x51 => (1,(0,(0,(0,(1,(0,(1,0))))))) | x52 => (0,(1,(0,(0,(1,(0,(1,0))))))) | x53 => (1,(1,(0,(0,(1,(0,(1,0))))))) | x54 => (0,(0,(1,(0,(1,(0,(1,0))))))) | x55 => (1,(0,(1,(0,(1,(0,(1,0))))))) | x56 => (0,(1,(1,(0,(1,(0,(1,0))))))) | x57 => (1,(1,(1,(0,(1,(0,(1,0))))))) | x58 => (0,(0,(0,(1,(1,(0,(1,0))))))) | x59 => (1,(0,(0,(1,(1,(0,(1,0))))))) | x5a => (0,(1,(0,(1,(1,(0,(1,0))))))) | x5b => (1,(1,(0,(1,(1,(0,(1,0))))))) | x5c => (0,(0,(1,(1,(1,(0,(1,0))))))) | x5d => (1,(0,(1,(1,(1,(0,(1,0))))))) | x5e => (0,(1,(1,(1,(1,(0,(1,0))))))) | x5f => (1,(1,(1,(1,(1,(0,(1,0))))))) | x60 => (0,(0,(0,(0,(0,(1,(1,0))))))) | x61 => (1,(0,(0,(0,(0,(1,(1,0))))))) | x62 => (0,(1,(0,(0,(0,(1,(1,0))))))) | x63 => (1,(1,(0,(0,(0,(1,(1,0))))))) | x64 => (0,(0,(1,(0,(0,(1,(1,0))))))) | x65 => (1,(0,(1,(0,(0,(1,(1,0))))))) | x66 => (0,(1,(1,(0,(0,(1,(1,0))))))) | x67 => (1,(1,(1,(0,(0,(1,(1,0))))))) | x68 => (0,(0,(0,(1,(0,(1,(1,0))))))) | x69 => (1,(0,(0,(1,(0,(1,(1,0))))))) | x6a => (0,(1,(0,(1,(0,(1,(1,0))))))) | x6b => (1,(1,(0,(1,(0,(1,(1,0))))))) | x6c => (0,(0,(1,(1,(0,(1,(1,0))))))) | x6d => (1,(0,(1,(1,(0,(1,(1,0))))))) | x6e => (0,(1,(1,(1,(0,(1,(1,0))))))) | x6f => (1,(1,(1,(1,(0,(1,(1,0))))))) | x70 => (0,(0,(0,(0,(1,(1,(1,0))))))) | x71 => (1,(0,(0,(0,(1,(1,(1,0))))))) | x72 => (0,(1,(0,(0,(1,(1,(1,0))))))) | x73 => (1,(1,(0,(0,(1,(1,(1,0))))))) | x74 => (0,(0,(1,(0,(1,(1,(1,0))))))) | x75 => (1,(0,(1,(0,(1,(1,(1,0))))))) | x76 => (0,(1,(1,(0,(1,(1,(1,0))))))) | x77 => (1,(1,(1,(0,(1,(1,(1,0))))))) | x78 => (0,(0,(0,(1,(1,(1,(1,0))))))) | x79 => (1,(0,(0,(1,(1,(1,(1,0))))))) | x7a => (0,(1,(0,(1,(1,(1,(1,0))))))) | x7b => (1,(1,(0,(1,(1,(1,(1,0))))))) | x7c => (0,(0,(1,(1,(1,(1,(1,0))))))) | x7d => (1,(0,(1,(1,(1,(1,(1,0))))))) | x7e => (0,(1,(1,(1,(1,(1,(1,0))))))) | x7f => (1,(1,(1,(1,(1,(1,(1,0))))))) | x80 => (0,(0,(0,(0,(0,(0,(0,1))))))) | x81 => (1,(0,(0,(0,(0,(0,(0,1))))))) | x82 => (0,(1,(0,(0,(0,(0,(0,1))))))) | x83 => (1,(1,(0,(0,(0,(0,(0,1))))))) | x84 => (0,(0,(1,(0,(0,(0,(0,1))))))) | x85 => (1,(0,(1,(0,(0,(0,(0,1))))))) | x86 => (0,(1,(1,(0,(0,(0,(0,1))))))) | x87 => (1,(1,(1,(0,(0,(0,(0,1))))))) | x88 => (0,(0,(0,(1,(0,(0,(0,1))))))) | x89 => (1,(0,(0,(1,(0,(0,(0,1))))))) | x8a => (0,(1,(0,(1,(0,(0,(0,1))))))) | x8b => (1,(1,(0,(1,(0,(0,(0,1))))))) | x8c => (0,(0,(1,(1,(0,(0,(0,1))))))) | x8d => (1,(0,(1,(1,(0,(0,(0,1))))))) | x8e => (0,(1,(1,(1,(0,(0,(0,1))))))) | x8f => (1,(1,(1,(1,(0,(0,(0,1))))))) | x90 => (0,(0,(0,(0,(1,(0,(0,1))))))) | x91 => (1,(0,(0,(0,(1,(0,(0,1))))))) | x92 => (0,(1,(0,(0,(1,(0,(0,1))))))) | x93 => (1,(1,(0,(0,(1,(0,(0,1))))))) | x94 => (0,(0,(1,(0,(1,(0,(0,1))))))) | x95 => (1,(0,(1,(0,(1,(0,(0,1))))))) | x96 => (0,(1,(1,(0,(1,(0,(0,1))))))) | x97 => (1,(1,(1,(0,(1,(0,(0,1))))))) | x98 => (0,(0,(0,(1,(1,(0,(0,1))))))) | x99 => (1,(0,(0,(1,(1,(0,(0,1))))))) | x9a => (0,(1,(0,(1,(1,(0,(0,1))))))) | x9b => (1,(1,(0,(1,(1,(0,(0,1))))))) | x9c => (0,(0,(1,(1,(1,(0,(0,1))))))) | x9d => (1,(0,(1,(1,(1,(0,(0,1))))))) | x9e => (0,(1,(1,(1,(1,(0,(0,1))))))) | x9f => (1,(1,(1,(1,(1,(0,(0,1))))))) | xa0 => (0,(0,(0,(0,(0,(1,(0,1))))))) | xa1 => (1,(0,(0,(0,(0,(1,(0,1))))))) | xa2 => (0,(1,(0,(0,(0,(1,(0,1))))))) | xa3 => (1,(1,(0,(0,(0,(1,(0,1))))))) | xa4 => (0,(0,(1,(0,(0,(1,(0,1))))))) | xa5 => (1,(0,(1,(0,(0,(1,(0,1))))))) | xa6 => (0,(1,(1,(0,(0,(1,(0,1))))))) | xa7 => (1,(1,(1,(0,(0,(1,(0,1))))))) | xa8 => (0,(0,(0,(1,(0,(1,(0,1))))))) | xa9 => (1,(0,(0,(1,(0,(1,(0,1))))))) | xaa => (0,(1,(0,(1,(0,(1,(0,1))))))) | xab => (1,(1,(0,(1,(0,(1,(0,1))))))) | xac => (0,(0,(1,(1,(0,(1,(0,1))))))) | xad => (1,(0,(1,(1,(0,(1,(0,1))))))) | xae => (0,(1,(1,(1,(0,(1,(0,1))))))) | xaf => (1,(1,(1,(1,(0,(1,(0,1))))))) | xb0 => (0,(0,(0,(0,(1,(1,(0,1))))))) | xb1 => (1,(0,(0,(0,(1,(1,(0,1))))))) | xb2 => (0,(1,(0,(0,(1,(1,(0,1))))))) | xb3 => (1,(1,(0,(0,(1,(1,(0,1))))))) | xb4 => (0,(0,(1,(0,(1,(1,(0,1))))))) | xb5 => (1,(0,(1,(0,(1,(1,(0,1))))))) | xb6 => (0,(1,(1,(0,(1,(1,(0,1))))))) | xb7 => (1,(1,(1,(0,(1,(1,(0,1))))))) | xb8 => (0,(0,(0,(1,(1,(1,(0,1))))))) | xb9 => (1,(0,(0,(1,(1,(1,(0,1))))))) | xba => (0,(1,(0,(1,(1,(1,(0,1))))))) | xbb => (1,(1,(0,(1,(1,(1,(0,1))))))) | xbc => (0,(0,(1,(1,(1,(1,(0,1))))))) | xbd => (1,(0,(1,(1,(1,(1,(0,1))))))) | xbe => (0,(1,(1,(1,(1,(1,(0,1))))))) | xbf => (1,(1,(1,(1,(1,(1,(0,1))))))) | xc0 => (0,(0,(0,(0,(0,(0,(1,1))))))) | xc1 => (1,(0,(0,(0,(0,(0,(1,1))))))) | xc2 => (0,(1,(0,(0,(0,(0,(1,1))))))) | xc3 => (1,(1,(0,(0,(0,(0,(1,1))))))) | xc4 => (0,(0,(1,(0,(0,(0,(1,1))))))) | xc5 => (1,(0,(1,(0,(0,(0,(1,1))))))) | xc6 => (0,(1,(1,(0,(0,(0,(1,1))))))) | xc7 => (1,(1,(1,(0,(0,(0,(1,1))))))) | xc8 => (0,(0,(0,(1,(0,(0,(1,1))))))) | xc9 => (1,(0,(0,(1,(0,(0,(1,1))))))) | xca => (0,(1,(0,(1,(0,(0,(1,1))))))) | xcb => (1,(1,(0,(1,(0,(0,(1,1))))))) | xcc => (0,(0,(1,(1,(0,(0,(1,1))))))) | xcd => (1,(0,(1,(1,(0,(0,(1,1))))))) | xce => (0,(1,(1,(1,(0,(0,(1,1))))))) | xcf => (1,(1,(1,(1,(0,(0,(1,1))))))) | xd0 => (0,(0,(0,(0,(1,(0,(1,1))))))) | xd1 => (1,(0,(0,(0,(1,(0,(1,1))))))) | xd2 => (0,(1,(0,(0,(1,(0,(1,1))))))) | xd3 => (1,(1,(0,(0,(1,(0,(1,1))))))) | xd4 => (0,(0,(1,(0,(1,(0,(1,1))))))) | xd5 => (1,(0,(1,(0,(1,(0,(1,1))))))) | xd6 => (0,(1,(1,(0,(1,(0,(1,1))))))) | xd7 => (1,(1,(1,(0,(1,(0,(1,1))))))) | xd8 => (0,(0,(0,(1,(1,(0,(1,1))))))) | xd9 => (1,(0,(0,(1,(1,(0,(1,1))))))) | xda => (0,(1,(0,(1,(1,(0,(1,1))))))) | xdb => (1,(1,(0,(1,(1,(0,(1,1))))))) | xdc => (0,(0,(1,(1,(1,(0,(1,1))))))) | xdd => (1,(0,(1,(1,(1,(0,(1,1))))))) | xde => (0,(1,(1,(1,(1,(0,(1,1))))))) | xdf => (1,(1,(1,(1,(1,(0,(1,1))))))) | xe0 => (0,(0,(0,(0,(0,(1,(1,1))))))) | xe1 => (1,(0,(0,(0,(0,(1,(1,1))))))) | xe2 => (0,(1,(0,(0,(0,(1,(1,1))))))) | xe3 => (1,(1,(0,(0,(0,(1,(1,1))))))) | xe4 => (0,(0,(1,(0,(0,(1,(1,1))))))) | xe5 => (1,(0,(1,(0,(0,(1,(1,1))))))) | xe6 => (0,(1,(1,(0,(0,(1,(1,1))))))) | xe7 => (1,(1,(1,(0,(0,(1,(1,1))))))) | xe8 => (0,(0,(0,(1,(0,(1,(1,1))))))) | xe9 => (1,(0,(0,(1,(0,(1,(1,1))))))) | xea => (0,(1,(0,(1,(0,(1,(1,1))))))) | xeb => (1,(1,(0,(1,(0,(1,(1,1))))))) | xec => (0,(0,(1,(1,(0,(1,(1,1))))))) | xed => (1,(0,(1,(1,(0,(1,(1,1))))))) | xee => (0,(1,(1,(1,(0,(1,(1,1))))))) | xef => (1,(1,(1,(1,(0,(1,(1,1))))))) | xf0 => (0,(0,(0,(0,(1,(1,(1,1))))))) | xf1 => (1,(0,(0,(0,(1,(1,(1,1))))))) | xf2 => (0,(1,(0,(0,(1,(1,(1,1))))))) | xf3 => (1,(1,(0,(0,(1,(1,(1,1))))))) | xf4 => (0,(0,(1,(0,(1,(1,(1,1))))))) | xf5 => (1,(0,(1,(0,(1,(1,(1,1))))))) | xf6 => (0,(1,(1,(0,(1,(1,(1,1))))))) | xf7 => (1,(1,(1,(0,(1,(1,(1,1))))))) | xf8 => (0,(0,(0,(1,(1,(1,(1,1))))))) | xf9 => (1,(0,(0,(1,(1,(1,(1,1))))))) | xfa => (0,(1,(0,(1,(1,(1,(1,1))))))) | xfb => (1,(1,(0,(1,(1,(1,(1,1))))))) | xfc => (0,(0,(1,(1,(1,(1,(1,1))))))) | xfd => (1,(0,(1,(1,(1,(1,(1,1))))))) | xfe => (0,(1,(1,(1,(1,(1,(1,1))))))) | xff => (1,(1,(1,(1,(1,(1,(1,1))))))) end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Byte.v\", \"module\": [], \"line\": 554}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma of_bits_to_bits (b : byte) : of_bits (to_bits b) = b.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Byte.v\", \"module\": [], \"line\": 814}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma to_bits_of_bits (b : _) : to_bits (of_bits b) = b.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Byte.v\", \"module\": [], \"line\": 817}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition byte_of_byte (b : byte) : byte := b.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Byte.v\", \"module\": [], \"line\": 826}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_S := f_equal S.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 36}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition f_equal_nat := f_equal (A:=nat).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 37}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition f_equal_pred := f_equal pred.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 46}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem pred_Sn : forall n:nat, n = pred (S n).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 48}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition eq_add_S n m (H: S n = S m): n = m := f_equal pred H.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 55}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem not_eq_S : forall n m:nat, n <> m -> S n <> S m.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 59}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition IsSucc (n:nat) : Prop := match n with | O => False | S p => True end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 66}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem O_S : forall n:nat, 0 <> S n.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 74}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem n_Sn : forall n:nat, n <> S n.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 81}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation plus := Nat.add (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 90}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Infix \\\"+\\\" := Nat.add : nat_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 91}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition f_equal2_plus := f_equal2 plus.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 93}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition f_equal2_nat := f_equal2 (A1:=nat) (A2:=nat).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 94}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma plus_n_O : forall n:nat, n = n + 0.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 98}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma plus_O_n : forall n:nat, 0 + n = n.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 108}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma plus_n_Sm : forall n m:nat, S (n + m) = n + S m.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 113}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma plus_Sn_m : forall n m:nat, S n + m = S (n + m).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 120}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation plus_0_r_reverse := plus_n_O (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 127}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation plus_succ_r_reverse := plus_n_Sm (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 128}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation mult := Nat.mul (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 132}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Infix \\\"*\\\" := Nat.mul : nat_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 133}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition f_equal2_mult := f_equal2 mult.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 135}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma mult_n_O : forall n:nat, 0 = n * 0.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 139}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma mult_n_Sm : forall n m:nat, n * m + n = n * S m.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 146}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation mult_0_r_reverse := mult_n_O (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 157}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation mult_succ_r_reverse := mult_n_Sm (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 158}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation minus := Nat.sub (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 162}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Infix \\\"-\\\" := Nat.sub : nat_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 163}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"Inductive le (n:nat) : nat -> Prop := | le_n : n <= n | le_S : forall m:nat, n <= m -> n <= S m where \\\"n <= m\\\" := (le n m) : nat_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 168}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Inductive le (n:nat) : nat -> Prop := | le_n : n <= n | le_S : forall m:nat, n <= m -> n <= S m where \\\"n <= m\\\" := (le n m) : nat_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 168}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition lt (n m:nat) := S n <= m.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 180}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Infix \\\"<\\\" := lt : nat_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 184}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition ge (n m:nat) := m <= n.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 186}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Infix \\\">=\\\" := ge : nat_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 190}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition gt (n m:nat) := m < n.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 192}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Infix \\\">\\\" := gt : nat_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 196}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"x <= y <= z\\\" := (x <= y /\\\\ y <= z) : nat_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 198}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"x <= y < z\\\" := (x <= y /\\\\ y < z) : nat_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 199}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"x < y < z\\\" := (x < y /\\\\ y < z) : nat_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 200}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation \\\"x < y <= z\\\" := (x < y /\\\\ y <= z) : nat_scope.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 201}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem le_pred : forall n m, n <= m -> pred n <= pred m.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 208}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem le_S_n : forall n m, S n <= S m -> n <= m.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 213}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem le_0_n : forall n, 0 <= n.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 218}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem le_n_S : forall n m, n <= m -> S n <= S m.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 223}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem nat_case : forall (n:nat) (P:nat -> Prop), P 0 -> (forall m:nat, P (S m)) -> P n.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 230}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem nat_double_ind : forall R:nat -> nat -> Prop, (forall n:nat, R 0 n) -> (forall n:nat, R (S n) 0) -> (forall n m:nat, R n m -> R (S n) (S m)) -> forall n m:nat, R n m.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 238}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma max_l n m : m <= n -> Nat.max n m = n.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 254}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma max_r n m : n <= m -> Nat.max n m = m.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 261}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma min_l n m : n <= m -> Nat.min n m = n.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 268}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma min_r n m : m <= n -> Nat.min n m = m.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 275}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma nat_rect_succ_r {A} (f: A -> A) (x:A) n : nat_rect (fun _ => A) x (fun _ => f) (S n) = nat_rect (fun _ => A) (f x) (fun _ => f) n.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 283}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem nat_rect_plus : forall (n m:nat) {A} (f:A -> A) (x:A), nat_rect (fun _ => A) x (fun _ => f) (n + m) = nat_rect (fun _ => A) (nat_rect (fun _ => A) x (fun _ => f) m) (fun _ => f) n.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Peano.v\", \"module\": [], \"line\": 289}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"Inductive Acc (x: A) : Prop := Acc_intro : (forall y:A, R y x -> Acc y) -> Acc x.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Wf.v\", \"module\": [], \"line\": 32}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma Acc_inv : forall x:A, Acc x -> forall y:A, R y x -> Acc y.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Wf.v\", \"module\": [], \"line\": 37}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition well_founded := forall a:A, Acc a.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Wf.v\", \"module\": [], \"line\": 46}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem well_founded_induction_type : forall P:A -> Type, (forall x:A, (forall y:A, R y x -> P y) -> P x) -> forall a:A, P a.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Wf.v\", \"module\": [], \"line\": 54}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem well_founded_induction : forall P:A -> Set, (forall x:A, (forall y:A, R y x -> P y) -> P x) -> forall a:A, P a.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Wf.v\", \"module\": [], \"line\": 61}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem well_founded_ind : forall P:A -> Prop, (forall x:A, (forall y:A, R y x -> P y) -> P x) -> forall a:A, P a.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Wf.v\", \"module\": [], \"line\": 68}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint Fix_F (x:A) (a:Acc x) : P x := F (fun (y:A) (h:R y x) => Fix_F (Acc_inv a h)).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Wf.v\", \"module\": [], \"line\": 82}",
    "{\"type\": \"TermType.SCHEME\", \"text\": \"Scheme Acc_inv_dep := Induction for Acc Sort Prop.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Wf.v\", \"module\": [], \"line\": 85}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma Fix_F_eq (x:A) (r:Acc x) : F (fun (y:A) (p:R y x) => Fix_F (x:=y) (Acc_inv r p)) = Fix_F (x:=x) r.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Wf.v\", \"module\": [], \"line\": 87}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition Fix (x:A) := Fix_F (Rwf x).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Wf.v\", \"module\": [], \"line\": 93}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma Fix_F_inv : forall (x:A) (r s:Acc x), Fix_F r = Fix_F s.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Wf.v\", \"module\": [], \"line\": 103}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma Fix_eq : forall x:A, Fix x = F (fun (y:A) (p:R y x) => Fix y).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Wf.v\", \"module\": [], \"line\": 110}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint Fix_F_2 (x:A) (x':B) (a:Acc R (x, x')) : P x x' := F (fun (y:A) (y':B) (h:R (y, y') (x, x')) => Fix_F_2 (x:=y) (x':=y') (Acc_inv a (y,y') h)).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Wf.v\", \"module\": [], \"line\": 138}",
    "{\"type\": \"TermType.THEOREM\", \"text\": \"Theorem well_founded_induction_type_2 : (forall (x:A) (x':B), (forall (y:A) (y':B), R (y, y') (x, x') -> P y y') -> P x x') -> forall (a:A) (b:B), P a b.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Wf.v\", \"module\": [], \"line\": 147}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation Acc_iter := Fix_F (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Wf.v\", \"module\": [], \"line\": 157}",
    "{\"type\": \"TermType.NOTATION\", \"text\": \"Notation Acc_iter_2 := Fix_F_2 (only parsing).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Wf.v\", \"module\": [], \"line\": 158}",
    "{\"type\": \"TermType.FIXPOINT\", \"text\": \"Fixpoint Acc_intro_generator n (wf : well_founded R) := match n with | O => wf | S n => fun x => Acc_intro x (fun y _ => Acc_intro_generator n (Acc_intro_generator n wf) y) end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Wf.v\", \"module\": [], \"line\": 171}",
    "{\"type\": \"TermType.TACTIC\", \"text\": \"Ltac exfalso := Coq.Init.Ltac.exfalso.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Tactics.v\", \"module\": [], \"line\": 20}",
    "{\"type\": \"TermType.TACTIC\", \"text\": \"Ltac contradict H := let save tac H := let x:=fresh in intro x; tac H; rename x into H in let negpos H := case H; clear H in let negneg H := save negpos H in let pospos H := let A := type of H in (exfalso; revert H; try fold (~A)) in let posneg H := save pospos H in let neg H := match goal with | |- (~_) => negneg H | |- (_->False) => negneg H | |- _ => negpos H end in let pos H := match goal with | |- (~_) => posneg H | |- (_->False) => posneg H | |- _ => pospos H end in match type of H with | (~_) => neg H | (_->False) => neg H | _ => (elim H;fail) || pos H end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Tactics.v\", \"module\": [], \"line\": 31}",
    "{\"type\": \"TermType.TACTIC\", \"text\": \"Ltac false_hyp H G := let T := type of H in absurd T; [ apply G | assumption ].\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Tactics.v\", \"module\": [], \"line\": 61}",
    "{\"type\": \"TermType.TACTIC\", \"text\": \"Ltac case_eq x := generalize (eq_refl x); pattern x at -1; case x.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Tactics.v\", \"module\": [], \"line\": 66}",
    "{\"type\": \"TermType.TACTIC\", \"text\": \"Ltac destr_eq H := discriminate H || (try (injection H as [= H])).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Tactics.v\", \"module\": [], \"line\": 70}",
    "{\"type\": \"TermType.TACTIC\", \"text\": \"Ltac destruct_all t := match goal with | x : t |- _ => destruct x; destruct_all t | _ => idtac end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Tactics.v\", \"module\": [], \"line\": 85}",
    "{\"type\": \"TermType.TACTIC\", \"text\": \"Ltac find_equiv H := let T := type of H in lazymatch T with | ?A -> ?B => let H1 := fresh in let H2 := fresh in cut A; [intro H1; pose proof (H H1) as H2; clear H H1; rename H2 into H; find_equiv H | clear H] | forall x : ?t, _ => let a := fresh \\\"a\\\" in let H1 := fresh \\\"H\\\" in evar (a : t); pose proof (H a) as H1; unfold a in H1; clear a; clear H; rename H1 into H; find_equiv H | ?A <-> ?B => idtac | _ => fail \\\"The given statement does not seem to end with an equivalence.\\\" end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Tactics.v\", \"module\": [], \"line\": 118}",
    "{\"type\": \"TermType.TACTIC\", \"text\": \"Ltac bapply lemma todo := let H := fresh in pose proof lemma as H; find_equiv H; [todo H; clear H | .. ].\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Tactics.v\", \"module\": [], \"line\": 137}",
    "{\"type\": \"TermType.TACTIC\", \"text\": \"Ltac easy := let rec use_hyp H := match type of H with | _ /\\\\ _ => exact H || destruct_hyp H | _ => try solve [inversion H] end with do_intro := let H := fresh in intro H; use_hyp H with destruct_hyp H := case H; clear H; do_intro; do_intro in let rec use_hyps := match goal with | H : _ /\\\\ _ |- _ => exact H || (destruct_hyp H; use_hyps) | H : _ |- _ => solve [inversion H] | _ => idtac end in let do_atom := solve [ trivial with eq_true | reflexivity | symmetry; trivial | contradiction ] in let rec do_ccl := try do_atom; repeat (do_intro; try do_atom); solve [ split; do_ccl ] in solve [ do_atom | use_hyps; do_ccl ] || fail \\\"Cannot solve this goal\\\".\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Tactics.v\", \"module\": [], \"line\": 157}",
    "{\"type\": \"TermType.TACTIC\", \"text\": \"Ltac easy' := repeat split; simpl; easy || now destruct 1.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Tactics.v\", \"module\": [], \"line\": 184}",
    "{\"type\": \"TermType.TACTIC\", \"text\": \"Ltac now_show c := change c.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Tactics.v\", \"module\": [], \"line\": 188}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma decide_left : forall (C:Prop) (decide:{C}+{~C}), C -> forall P:{C}+{~C}->Prop, (forall H:C, P (left _ H)) -> P decide.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Tactics.v\", \"module\": [], \"line\": 194}",
    "{\"type\": \"TermType.LEMMA\", \"text\": \"Lemma decide_right : forall (C:Prop) (decide:{C}+{~C}), ~C -> forall P:{C}+{~C}->Prop, (forall H:~C, P (right _ H)) -> P decide.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Tactics.v\", \"module\": [], \"line\": 202}",
    "{\"type\": \"TermType.TACTIC\", \"text\": \"Ltac lookup_inversion_sigma_rect H := lazymatch type of H with | ex_intro _ _ _ = ex_intro _ _ _ => uconstr:(eq_ex_rect_ex_intro) | exist _ _ _ = exist _ _ _ => uconstr:(eq_sig_rect_exist) | existT _ _ _ = existT _ _ _ => uconstr:(eq_sigT_rect_existT) | _ = ex_intro _ _ _ => uconstr:(eq_ex_rect_ex_intro_r) | _ = exist _ _ _ => uconstr:(eq_sig_rect_exist_r) | _ = existT _ _ _ => uconstr:(eq_sigT_rect_existT_r) | ex_intro _ _ _ = _ => uconstr:(eq_ex_rect_ex_intro_l) | exist _ _ _ = _ => uconstr:(eq_sig_rect_exist_l) | existT _ _ _ = _ => uconstr:(eq_sigT_rect_existT_l) | ex_intro2 _ _ _ _ _ = ex_intro2 _ _ _ _ _ => uconstr:(eq_ex2_rect_ex_intro2) | exist2 _ _ _ _ _ = exist2 _ _ _ _ _ => uconstr:(eq_sig2_rect_exist2) | existT2 _ _ _ _ _ = existT2 _ _ _ _ _ => uconstr:(eq_sigT2_rect_existT2) | _ = ex_intro2 _ _ _ _ _ => uconstr:(eq_ex2_rect_ex_intro2_r) | _ = exist2 _ _ _ _ _ => uconstr:(eq_sig2_rect_exist2_r) | _ = existT2 _ _ _ _ _ => uconstr:(eq_sigT2_rect_existT2_r) | ex_intro2 _ _ _ _ _ = _ => uconstr:(eq_ex2_rect_ex_intro2_l) | exist2 _ _ _ _ _ = _ => uconstr:(eq_sig2_rect_exist2_l) | existT2 _ _ _ _ _ = _ => uconstr:(eq_sigT2_rect_existT2_l) | _ = _ :> ?T => let sig := uconstr:(@sig) in let sig2 := uconstr:(@sig2) in let sigT := uconstr:(@sigT) in let sigT2 := uconstr:(@sigT2) in let ex := uconstr:(@ex) in let ex2 := uconstr:(@ex2) in fail 0 \\\"Type\\\" \\\"of\\\" H \\\"is\\\" \\\"not\\\" \\\"an\\\" \\\"equality\\\" \\\"of\\\" \\\"recognized\\\" \\\"\\u03a3\\\" \\\"types:\\\" \\\"expected\\\" \\\"one\\\" \\\"of\\\" sig sig2 sigT sigT2 ex \\\"or\\\" ex2 \\\"but\\\" \\\"got\\\" T | _ => fail 0 H \\\"is\\\" \\\"not\\\" \\\"an\\\" \\\"equality\\\" \\\"of\\\" \\\"\\u03a3\\\" \\\"types\\\" end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Tactics.v\", \"module\": [], \"line\": 260}",
    "{\"type\": \"TermType.TACTIC\", \"text\": \"Ltac inversion_sigma_on_as H ip := let rect := lookup_inversion_sigma_rect H in induction H as ip using rect.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Tactics.v\", \"module\": [], \"line\": 309}",
    "{\"type\": \"TermType.TACTIC\", \"text\": \"Ltac inversion_sigma_on H := inversion_sigma_on_as H ipattern:([]).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Tactics.v\", \"module\": [], \"line\": 312}",
    "{\"type\": \"TermType.TACTIC\", \"text\": \"Ltac inversion_sigma_step := match goal with | [ H : _ |- _ ] => inversion_sigma_on H end.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Tactics.v\", \"module\": [], \"line\": 313}",
    "{\"type\": \"TermType.TACTIC\", \"text\": \"Ltac inversion_sigma := repeat inversion_sigma_step.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Tactics.v\", \"module\": [], \"line\": 317}",
    "{\"type\": \"TermType.TACTIC\", \"text\": \"Ltac time_constr tac := let eval_early := match goal with _ => restart_timer end in let ret := tac () in let eval_early := match goal with _ => finish_timing ( \\\"Tactic evaluation\\\" ) end in ret.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Tactics.v\", \"module\": [], \"line\": 325}",
    "{\"type\": \"TermType.TACTIC\", \"text\": \"Ltac assert_fails tac := tryif (once tac) then gfail 0 tac \\\"succeeds\\\" else idtac.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Tactics.v\", \"module\": [], \"line\": 333}",
    "{\"type\": \"TermType.TACTIC\", \"text\": \"Ltac tauto := with_uniform_flags ltac:(fun flags => tauto_gen flags).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Tauto.v\", \"module\": [], \"line\": 104}",
    "{\"type\": \"TermType.TACTIC\", \"text\": \"Ltac dtauto := with_power_flags ltac:(fun flags => tauto_gen flags).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Tauto.v\", \"module\": [], \"line\": 105}",
    "{\"type\": \"TermType.TACTIC\", \"text\": \"Ltac intuition_solver := first [solve [auto] | tryif solve [auto with *] then warn_auto_with_star else idtac].\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Tauto.v\", \"module\": [], \"line\": 107}",
    "{\"type\": \"TermType.TACTIC\", \"text\": \"Ltac intuition := intuition_then ltac:(idtac;intuition_solver).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Tauto.v\", \"module\": [], \"line\": 112}",
    "{\"type\": \"TermType.TACTIC\", \"text\": \"Ltac dintuition := dintuition_then ltac:(idtac;intuition_solver).\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Tauto.v\", \"module\": [], \"line\": 115}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"#[universes(polymorphic=yes)] Definition ReverseCoercionSource (T : Type) := T.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Prelude.v\", \"module\": [], \"line\": 61}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"#[universes(polymorphic=yes)] Definition ReverseCoercionTarget (T : Type) := T.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Prelude.v\", \"module\": [], \"line\": 62}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"#[warning=\\\"-uniform-inheritance\\\", reversible=no, universes(polymorphic=yes)] Coercion reverse_coercion {T' T} (x' : T') (x : ReverseCoercionSource T) : ReverseCoercionTarget T' := x'.\", \"file_path\": \"../root/.opam/default/lib/coq/theories/Init/Prelude.v\", \"module\": [], \"line\": 63}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"Inductive BinarySet : Set := | top | bottom.\", \"file_path\": \"repos/yalhessi-verified-verifier/BinaryLattice.v\", \"module\": [], \"line\": 2}",
    "{\"type\": \"TermType.INDUCTIVE\", \"text\": \"Inductive BinaryRel : BinarySet -> BinarySet -> Prop := | bot_rel x : BinaryRel bottom x | top_rel x : BinaryRel x top.\", \"file_path\": \"repos/yalhessi-verified-verifier/BinaryLattice.v\", \"module\": [], \"line\": 6}",
    "{\"type\": \"TermType.INSTANCE\", \"text\": \"Program Instance BinaryOrder : Order BinarySet := { ord := BinaryRel }.\", \"file_path\": \"repos/yalhessi-verified-verifier/BinaryLattice.v\", \"module\": [], \"line\": 10}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.\", \"file_path\": \"repos/yalhessi-verified-verifier/BinaryLattice.v\", \"module\": [], \"line\": 24}",
    "{\"type\": \"TermType.DEFINITION\", \"text\": \"Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.\", \"file_path\": \"repos/yalhessi-verified-verifier/BinaryLattice.v\", \"module\": [], \"line\": 30}",
    "{\"type\": \"TermType.INSTANCE\", \"text\": \"Program Instance BinaryLattice : Lattice BinarySet := { meet := meet_BinarySet; join := join_BinarySet; (*meet_commutative : forall a b, a \\u2293 b = b \\u2293 a; meet_associative : forall a b c, (a \\u2293 b) \\u2293 c = a \\u2293 (b \\u2293 c); meet_absorptive : forall a b, a \\u2293 (a \\u2294 b) = a; meet_idempotent : forall a, a \\u2293 a = a; join_commutative : forall a b, a \\u2294 b = b \\u2294 a; join_associative : forall a b c, (a \\u2294 b) \\u2294 c = a \\u2294 (b \\u2294 c); join_absorptive : forall a b, a \\u2294 (a \\u2293 b) = a; join_idempotent : forall a, a \\u2294 a = a*) }.\", \"file_path\": \"repos/yalhessi-verified-verifier/BinaryLattice.v\", \"module\": [], \"line\": 36}",
    "{\"type\": \"TermType.INSTANCE\", \"text\": \"Program Instance BinaryLOSet : LOSet BinaryOrder BinaryLattice.\", \"file_path\": \"repos/yalhessi-verified-verifier/BinaryLattice.v\", \"module\": [], \"line\": 76}"
  ],
  "proofs": [
    {
      "theorem": {
        "type": "TermType.OBLIGATION",
        "text": "Next Obligation.",
        "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
        "module": [],
        "line": 11,
        "context": [
          {
            "type": "TermType.INDUCTIVE",
            "text": "Inductive BinarySet : Set := | top | bottom.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 2
          },
          {
            "type": "TermType.INDUCTIVE",
            "text": "Inductive BinaryRel : BinarySet -> BinarySet -> Prop := | bot_rel x : BinaryRel bottom x | top_rel x : BinaryRel x top.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 6
          }
        ]
      },
      "steps": [
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 11,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinaryRel : BinarySet -> BinarySet -> Prop := | bot_rel x : BinaryRel bottom x | top_rel x : BinaryRel x top.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 6
              }
            ]
          },
          "step": {
            "text": "\n  unfold RelationClasses.Reflexive.",
            "context": []
          },
          "n_step": 1,
          "goals": [
            "\n\nRelationClasses.Reflexive BinaryRel"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 11,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinaryRel : BinarySet -> BinarySet -> Prop := | bot_rel x : BinaryRel bottom x | top_rel x : BinaryRel x top.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 6
              }
            ]
          },
          "step": {
            "text": "\n  intros x.",
            "context": []
          },
          "n_step": 2,
          "goals": [
            "\n\nforall x : BinarySet, BinaryRel x x"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 11,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinaryRel : BinarySet -> BinarySet -> Prop := | bot_rel x : BinaryRel bottom x | top_rel x : BinaryRel x top.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 6
              }
            ]
          },
          "step": {
            "text": " destruct x.",
            "context": []
          },
          "n_step": 3,
          "goals": [
            "x: BinarySet\n\nBinaryRel x x"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 11,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinaryRel : BinarySet -> BinarySet -> Prop := | bot_rel x : BinaryRel bottom x | top_rel x : BinaryRel x top.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 6
              }
            ]
          },
          "step": {
            "text": " apply top_rel.",
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinaryRel : BinarySet -> BinarySet -> Prop := | bot_rel x : BinaryRel bottom x | top_rel x : BinaryRel x top.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 6
              }
            ]
          },
          "n_step": 4,
          "goals": [
            "\n\nBinaryRel top top",
            "\n\nBinaryRel bottom bottom"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 11,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinaryRel : BinarySet -> BinarySet -> Prop := | bot_rel x : BinaryRel bottom x | top_rel x : BinaryRel x top.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 6
              }
            ]
          },
          "step": {
            "text": " apply bot_rel.",
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinaryRel : BinarySet -> BinarySet -> Prop := | bot_rel x : BinaryRel bottom x | top_rel x : BinaryRel x top.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 6
              }
            ]
          },
          "n_step": 5,
          "goals": [
            "\n\nBinaryRel bottom bottom"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 11,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinaryRel : BinarySet -> BinarySet -> Prop := | bot_rel x : BinaryRel bottom x | top_rel x : BinaryRel x top.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 6
              }
            ]
          },
          "step": {
            "text": " \nDefined.",
            "context": []
          },
          "n_step": 6,
          "goals": []
        }
      ]
    },
    {
      "theorem": {
        "type": "TermType.OBLIGATION",
        "text": "Next Obligation.",
        "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
        "module": [],
        "line": 15,
        "context": [
          {
            "type": "TermType.INDUCTIVE",
            "text": "Inductive BinarySet : Set := | top | bottom.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 2
          },
          {
            "type": "TermType.INDUCTIVE",
            "text": "Inductive BinaryRel : BinarySet -> BinarySet -> Prop := | bot_rel x : BinaryRel bottom x | top_rel x : BinaryRel x top.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 6
          }
        ]
      },
      "steps": [
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 15,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinaryRel : BinarySet -> BinarySet -> Prop := | bot_rel x : BinaryRel bottom x | top_rel x : BinaryRel x top.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 6
              }
            ]
          },
          "step": {
            "text": " Proof.",
            "context": []
          },
          "n_step": 1,
          "goals": [
            "x, y: BinarySet\nH: BinaryRel x y\nH0: BinaryRel y x\n\nx = y"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 15,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinaryRel : BinarySet -> BinarySet -> Prop := | bot_rel x : BinaryRel bottom x | top_rel x : BinaryRel x top.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 6
              }
            ]
          },
          "step": {
            "text": "\n  induction x; induction y; auto; inversion H; inversion H0.",
            "context": []
          },
          "n_step": 2,
          "goals": [
            "x, y: BinarySet\nH: BinaryRel x y\nH0: BinaryRel y x\n\nx = y"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 15,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinaryRel : BinarySet -> BinarySet -> Prop := | bot_rel x : BinaryRel bottom x | top_rel x : BinaryRel x top.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 6
              }
            ]
          },
          "step": {
            "text": "\nDefined.",
            "context": []
          },
          "n_step": 3,
          "goals": []
        }
      ]
    },
    {
      "theorem": {
        "type": "TermType.OBLIGATION",
        "text": "Next Obligation.",
        "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
        "module": [],
        "line": 18,
        "context": [
          {
            "type": "TermType.INDUCTIVE",
            "text": "Inductive BinarySet : Set := | top | bottom.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 2
          },
          {
            "type": "TermType.INDUCTIVE",
            "text": "Inductive BinaryRel : BinarySet -> BinarySet -> Prop := | bot_rel x : BinaryRel bottom x | top_rel x : BinaryRel x top.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 6
          }
        ]
      },
      "steps": [
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 18,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinaryRel : BinarySet -> BinarySet -> Prop := | bot_rel x : BinaryRel bottom x | top_rel x : BinaryRel x top.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 6
              }
            ]
          },
          "step": {
            "text": " Proof.",
            "context": []
          },
          "n_step": 1,
          "goals": [
            "\n\nRelationClasses.Transitive BinaryRel"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 18,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinaryRel : BinarySet -> BinarySet -> Prop := | bot_rel x : BinaryRel bottom x | top_rel x : BinaryRel x top.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 6
              }
            ]
          },
          "step": {
            "text": "\n  unfold RelationClasses.Transitive.",
            "context": []
          },
          "n_step": 2,
          "goals": [
            "\n\nRelationClasses.Transitive BinaryRel"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 18,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinaryRel : BinarySet -> BinarySet -> Prop := | bot_rel x : BinaryRel bottom x | top_rel x : BinaryRel x top.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 6
              }
            ]
          },
          "step": {
            "text": "\n  induction x; induction y; induction z; auto; intros; try apply self_rel;\n    try inversion H; try inversion H0.",
            "context": []
          },
          "n_step": 3,
          "goals": [
            "\n\nforall x y z : BinarySet, BinaryRel x y -> BinaryRel y z -> BinaryRel x z"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 18,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinaryRel : BinarySet -> BinarySet -> Prop := | bot_rel x : BinaryRel bottom x | top_rel x : BinaryRel x top.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 6
              }
            ]
          },
          "step": {
            "text": "\nDefined.",
            "context": []
          },
          "n_step": 4,
          "goals": []
        }
      ]
    },
    {
      "theorem": {
        "type": "TermType.OBLIGATION",
        "text": "Next Obligation.",
        "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
        "module": [],
        "line": 51,
        "context": [
          {
            "type": "TermType.INDUCTIVE",
            "text": "Inductive BinarySet : Set := | top | bottom.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 2
          },
          {
            "type": "TermType.DEFINITION",
            "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 24
          },
          {
            "type": "TermType.DEFINITION",
            "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 30
          }
        ]
      },
      "steps": [
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 51,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 24
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 30
              }
            ]
          },
          "step": {
            "text": "\n  unfold meet_BinarySet; induction a; induction b; auto.",
            "context": [
              {
                "type": "TermType.DEFINITION",
                "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 24
              }
            ]
          },
          "n_step": 1,
          "goals": [
            "a, b: BinarySet\n\nmeet_BinarySet a b = meet_BinarySet b a"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 51,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 24
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 30
              }
            ]
          },
          "step": {
            "text": "\nDefined.",
            "context": []
          },
          "n_step": 2,
          "goals": []
        }
      ]
    },
    {
      "theorem": {
        "type": "TermType.OBLIGATION",
        "text": "Next Obligation.",
        "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
        "module": [],
        "line": 54,
        "context": [
          {
            "type": "TermType.INDUCTIVE",
            "text": "Inductive BinarySet : Set := | top | bottom.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 2
          },
          {
            "type": "TermType.DEFINITION",
            "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 24
          },
          {
            "type": "TermType.DEFINITION",
            "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 30
          }
        ]
      },
      "steps": [
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 54,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 24
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 30
              }
            ]
          },
          "step": {
            "text": " Proof.",
            "context": []
          },
          "n_step": 1,
          "goals": [
            "a, b, c: BinarySet\n\nmeet_BinarySet (meet_BinarySet a b) c = meet_BinarySet a (meet_BinarySet b c)"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 54,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 24
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 30
              }
            ]
          },
          "step": {
            "text": "\n  unfold meet_BinarySet; induction a; induction b; induction c; auto.",
            "context": [
              {
                "type": "TermType.DEFINITION",
                "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 24
              }
            ]
          },
          "n_step": 2,
          "goals": [
            "a, b, c: BinarySet\n\nmeet_BinarySet (meet_BinarySet a b) c = meet_BinarySet a (meet_BinarySet b c)"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 54,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 24
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 30
              }
            ]
          },
          "step": {
            "text": "\nDefined.",
            "context": []
          },
          "n_step": 3,
          "goals": []
        }
      ]
    },
    {
      "theorem": {
        "type": "TermType.OBLIGATION",
        "text": "Next Obligation.",
        "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
        "module": [],
        "line": 57,
        "context": [
          {
            "type": "TermType.INDUCTIVE",
            "text": "Inductive BinarySet : Set := | top | bottom.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 2
          },
          {
            "type": "TermType.DEFINITION",
            "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 24
          },
          {
            "type": "TermType.DEFINITION",
            "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 30
          }
        ]
      },
      "steps": [
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 57,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 24
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 30
              }
            ]
          },
          "step": {
            "text": " Proof.",
            "context": []
          },
          "n_step": 1,
          "goals": [
            "a, b: BinarySet\n\nmeet_BinarySet a (join_BinarySet a b) = a"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 57,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 24
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 30
              }
            ]
          },
          "step": {
            "text": "\n  unfold meet_BinarySet; unfold join_BinarySet; induction a; induction b; auto.",
            "context": [
              {
                "type": "TermType.DEFINITION",
                "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 24
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 30
              }
            ]
          },
          "n_step": 2,
          "goals": [
            "a, b: BinarySet\n\nmeet_BinarySet a (join_BinarySet a b) = a"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 57,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 24
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 30
              }
            ]
          },
          "step": {
            "text": "\nDefined.",
            "context": []
          },
          "n_step": 3,
          "goals": []
        }
      ]
    },
    {
      "theorem": {
        "type": "TermType.OBLIGATION",
        "text": "Next Obligation.",
        "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
        "module": [],
        "line": 60,
        "context": [
          {
            "type": "TermType.INDUCTIVE",
            "text": "Inductive BinarySet : Set := | top | bottom.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 2
          },
          {
            "type": "TermType.DEFINITION",
            "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 24
          },
          {
            "type": "TermType.DEFINITION",
            "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 30
          }
        ]
      },
      "steps": [
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 60,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 24
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 30
              }
            ]
          },
          "step": {
            "text": " Proof.",
            "context": []
          },
          "n_step": 1,
          "goals": [
            "a: BinarySet\n\nmeet_BinarySet a a = a"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 60,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 24
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 30
              }
            ]
          },
          "step": {
            "text": "\n  unfold meet_BinarySet; induction a; auto.",
            "context": [
              {
                "type": "TermType.DEFINITION",
                "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 24
              }
            ]
          },
          "n_step": 2,
          "goals": [
            "a: BinarySet\n\nmeet_BinarySet a a = a"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 60,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 24
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 30
              }
            ]
          },
          "step": {
            "text": "\nDefined.",
            "context": []
          },
          "n_step": 3,
          "goals": []
        }
      ]
    },
    {
      "theorem": {
        "type": "TermType.OBLIGATION",
        "text": "Next Obligation.",
        "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
        "module": [],
        "line": 63,
        "context": [
          {
            "type": "TermType.INDUCTIVE",
            "text": "Inductive BinarySet : Set := | top | bottom.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 2
          },
          {
            "type": "TermType.DEFINITION",
            "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 24
          },
          {
            "type": "TermType.DEFINITION",
            "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 30
          }
        ]
      },
      "steps": [
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 63,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 24
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 30
              }
            ]
          },
          "step": {
            "text": " Proof.",
            "context": []
          },
          "n_step": 1,
          "goals": [
            "a, b: BinarySet\n\njoin_BinarySet a b = join_BinarySet b a"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 63,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 24
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 30
              }
            ]
          },
          "step": {
            "text": "\n  unfold join_BinarySet; induction a; induction b; auto.",
            "context": [
              {
                "type": "TermType.DEFINITION",
                "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 30
              }
            ]
          },
          "n_step": 2,
          "goals": [
            "a, b: BinarySet\n\njoin_BinarySet a b = join_BinarySet b a"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 63,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 24
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 30
              }
            ]
          },
          "step": {
            "text": "\nDefined.",
            "context": []
          },
          "n_step": 3,
          "goals": []
        }
      ]
    },
    {
      "theorem": {
        "type": "TermType.OBLIGATION",
        "text": "Next Obligation.",
        "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
        "module": [],
        "line": 66,
        "context": [
          {
            "type": "TermType.INDUCTIVE",
            "text": "Inductive BinarySet : Set := | top | bottom.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 2
          },
          {
            "type": "TermType.DEFINITION",
            "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 24
          },
          {
            "type": "TermType.DEFINITION",
            "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 30
          }
        ]
      },
      "steps": [
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 66,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 24
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 30
              }
            ]
          },
          "step": {
            "text": " Proof.",
            "context": []
          },
          "n_step": 1,
          "goals": [
            "a, b, c: BinarySet\n\njoin_BinarySet (join_BinarySet a b) c = join_BinarySet a (join_BinarySet b c)"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 66,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 24
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 30
              }
            ]
          },
          "step": {
            "text": "\n  unfold join_BinarySet; induction a; induction b; induction c; auto.",
            "context": [
              {
                "type": "TermType.DEFINITION",
                "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 30
              }
            ]
          },
          "n_step": 2,
          "goals": [
            "a, b, c: BinarySet\n\njoin_BinarySet (join_BinarySet a b) c = join_BinarySet a (join_BinarySet b c)"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 66,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 24
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 30
              }
            ]
          },
          "step": {
            "text": "\nDefined.",
            "context": []
          },
          "n_step": 3,
          "goals": []
        }
      ]
    },
    {
      "theorem": {
        "type": "TermType.OBLIGATION",
        "text": "Next Obligation.",
        "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
        "module": [],
        "line": 69,
        "context": [
          {
            "type": "TermType.INDUCTIVE",
            "text": "Inductive BinarySet : Set := | top | bottom.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 2
          },
          {
            "type": "TermType.DEFINITION",
            "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 24
          },
          {
            "type": "TermType.DEFINITION",
            "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 30
          }
        ]
      },
      "steps": [
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 69,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 24
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 30
              }
            ]
          },
          "step": {
            "text": " Proof.",
            "context": []
          },
          "n_step": 1,
          "goals": [
            "a, b: BinarySet\n\njoin_BinarySet a (meet_BinarySet a b) = a"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 69,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 24
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 30
              }
            ]
          },
          "step": {
            "text": "\n  unfold join_BinarySet; unfold meet_BinarySet; induction a; induction b; auto.",
            "context": [
              {
                "type": "TermType.DEFINITION",
                "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 30
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 24
              }
            ]
          },
          "n_step": 2,
          "goals": [
            "a, b: BinarySet\n\njoin_BinarySet a (meet_BinarySet a b) = a"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 69,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 24
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 30
              }
            ]
          },
          "step": {
            "text": "\nDefined.",
            "context": []
          },
          "n_step": 3,
          "goals": []
        }
      ]
    },
    {
      "theorem": {
        "type": "TermType.OBLIGATION",
        "text": "Next Obligation.",
        "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
        "module": [],
        "line": 72,
        "context": [
          {
            "type": "TermType.INDUCTIVE",
            "text": "Inductive BinarySet : Set := | top | bottom.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 2
          },
          {
            "type": "TermType.DEFINITION",
            "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 24
          },
          {
            "type": "TermType.DEFINITION",
            "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 30
          }
        ]
      },
      "steps": [
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 72,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 24
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 30
              }
            ]
          },
          "step": {
            "text": " Proof.",
            "context": []
          },
          "n_step": 1,
          "goals": [
            "a: BinarySet\n\njoin_BinarySet a a = a"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 72,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 24
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 30
              }
            ]
          },
          "step": {
            "text": "\n  unfold join_BinarySet; induction a; auto.",
            "context": [
              {
                "type": "TermType.DEFINITION",
                "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 30
              }
            ]
          },
          "n_step": 2,
          "goals": [
            "a: BinarySet\n\njoin_BinarySet a a = a"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 72,
            "context": [
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinarySet : Set := | top | bottom.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 2
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 24
              },
              {
                "type": "TermType.DEFINITION",
                "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 30
              }
            ]
          },
          "step": {
            "text": "\nDefined.",
            "context": []
          },
          "n_step": 3,
          "goals": []
        }
      ]
    },
    {
      "theorem": {
        "type": "TermType.OBLIGATION",
        "text": "Next Obligation.",
        "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
        "module": [],
        "line": 77,
        "context": [
          {
            "type": "TermType.INSTANCE",
            "text": "Program Instance BinaryOrder : Order BinarySet := { ord := BinaryRel }.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 10
          },
          {
            "type": "TermType.INSTANCE",
            "text": "Program Instance BinaryLattice : Lattice BinarySet := { meet := meet_BinarySet; join := join_BinarySet; (*meet_commutative : forall a b, a \u2293 b = b \u2293 a; meet_associative : forall a b c, (a \u2293 b) \u2293 c = a \u2293 (b \u2293 c); meet_absorptive : forall a b, a \u2293 (a \u2294 b) = a; meet_idempotent : forall a, a \u2293 a = a; join_commutative : forall a b, a \u2294 b = b \u2294 a; join_associative : forall a b c, (a \u2294 b) \u2294 c = a \u2294 (b \u2294 c); join_absorptive : forall a b, a \u2294 (a \u2293 b) = a; join_idempotent : forall a, a \u2294 a = a*) }.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 36
          }
        ]
      },
      "steps": [
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 77,
            "context": [
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryOrder : Order BinarySet := { ord := BinaryRel }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 10
              },
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryLattice : Lattice BinarySet := { meet := meet_BinarySet; join := join_BinarySet; (*meet_commutative : forall a b, a \u2293 b = b \u2293 a; meet_associative : forall a b c, (a \u2293 b) \u2293 c = a \u2293 (b \u2293 c); meet_absorptive : forall a b, a \u2293 (a \u2294 b) = a; meet_idempotent : forall a, a \u2293 a = a; join_commutative : forall a b, a \u2294 b = b \u2294 a; join_associative : forall a b c, (a \u2294 b) \u2294 c = a \u2294 (b \u2294 c); join_absorptive : forall a b, a \u2294 (a \u2293 b) = a; join_idempotent : forall a, a \u2294 a = a*) }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 36
              }
            ]
          },
          "step": {
            "text": "\n  split.",
            "context": []
          },
          "n_step": 1,
          "goals": [
            "a, b: BinarySet\n\nBinaryRel a b <-> a = meet_BinarySet a b"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 77,
            "context": [
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryOrder : Order BinarySet := { ord := BinaryRel }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 10
              },
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryLattice : Lattice BinarySet := { meet := meet_BinarySet; join := join_BinarySet; (*meet_commutative : forall a b, a \u2293 b = b \u2293 a; meet_associative : forall a b c, (a \u2293 b) \u2293 c = a \u2293 (b \u2293 c); meet_absorptive : forall a b, a \u2293 (a \u2294 b) = a; meet_idempotent : forall a, a \u2293 a = a; join_commutative : forall a b, a \u2294 b = b \u2294 a; join_associative : forall a b c, (a \u2294 b) \u2294 c = a \u2294 (b \u2294 c); join_absorptive : forall a b, a \u2294 (a \u2293 b) = a; join_idempotent : forall a, a \u2294 a = a*) }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 36
              }
            ]
          },
          "step": {
            "text": "\n  -",
            "context": []
          },
          "n_step": 2,
          "goals": [
            "a, b: BinarySet\n\nBinaryRel a b -> a = meet_BinarySet a b",
            "a, b: BinarySet\n\na = meet_BinarySet a b -> BinaryRel a b"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 77,
            "context": [
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryOrder : Order BinarySet := { ord := BinaryRel }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 10
              },
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryLattice : Lattice BinarySet := { meet := meet_BinarySet; join := join_BinarySet; (*meet_commutative : forall a b, a \u2293 b = b \u2293 a; meet_associative : forall a b c, (a \u2293 b) \u2293 c = a \u2293 (b \u2293 c); meet_absorptive : forall a b, a \u2293 (a \u2294 b) = a; meet_idempotent : forall a, a \u2293 a = a; join_commutative : forall a b, a \u2294 b = b \u2294 a; join_associative : forall a b c, (a \u2294 b) \u2294 c = a \u2294 (b \u2294 c); join_absorptive : forall a b, a \u2294 (a \u2293 b) = a; join_idempotent : forall a, a \u2294 a = a*) }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 36
              }
            ]
          },
          "step": {
            "text": " intros.",
            "context": []
          },
          "n_step": 3,
          "goals": [
            "a, b: BinarySet\n\nBinaryRel a b -> a = meet_BinarySet a b"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 77,
            "context": [
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryOrder : Order BinarySet := { ord := BinaryRel }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 10
              },
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryLattice : Lattice BinarySet := { meet := meet_BinarySet; join := join_BinarySet; (*meet_commutative : forall a b, a \u2293 b = b \u2293 a; meet_associative : forall a b c, (a \u2293 b) \u2293 c = a \u2293 (b \u2293 c); meet_absorptive : forall a b, a \u2293 (a \u2294 b) = a; meet_idempotent : forall a, a \u2293 a = a; join_commutative : forall a b, a \u2294 b = b \u2294 a; join_associative : forall a b c, (a \u2294 b) \u2294 c = a \u2294 (b \u2294 c); join_absorptive : forall a b, a \u2294 (a \u2293 b) = a; join_idempotent : forall a, a \u2294 a = a*) }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 36
              }
            ]
          },
          "step": {
            "text": " induction a; induction b; auto; unfold meet_BinarySet; inversion H.",
            "context": [
              {
                "type": "TermType.DEFINITION",
                "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 24
              }
            ]
          },
          "n_step": 4,
          "goals": [
            "a, b: BinarySet\nH: BinaryRel a b\n\na = meet_BinarySet a b"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 77,
            "context": [
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryOrder : Order BinarySet := { ord := BinaryRel }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 10
              },
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryLattice : Lattice BinarySet := { meet := meet_BinarySet; join := join_BinarySet; (*meet_commutative : forall a b, a \u2293 b = b \u2293 a; meet_associative : forall a b c, (a \u2293 b) \u2293 c = a \u2293 (b \u2293 c); meet_absorptive : forall a b, a \u2293 (a \u2294 b) = a; meet_idempotent : forall a, a \u2293 a = a; join_commutative : forall a b, a \u2294 b = b \u2294 a; join_associative : forall a b c, (a \u2294 b) \u2294 c = a \u2294 (b \u2294 c); join_absorptive : forall a b, a \u2294 (a \u2293 b) = a; join_idempotent : forall a, a \u2294 a = a*) }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 36
              }
            ]
          },
          "step": {
            "text": "\n  -",
            "context": []
          },
          "n_step": 5,
          "goals": []
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 77,
            "context": [
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryOrder : Order BinarySet := { ord := BinaryRel }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 10
              },
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryLattice : Lattice BinarySet := { meet := meet_BinarySet; join := join_BinarySet; (*meet_commutative : forall a b, a \u2293 b = b \u2293 a; meet_associative : forall a b c, (a \u2293 b) \u2293 c = a \u2293 (b \u2293 c); meet_absorptive : forall a b, a \u2293 (a \u2294 b) = a; meet_idempotent : forall a, a \u2293 a = a; join_commutative : forall a b, a \u2294 b = b \u2294 a; join_associative : forall a b c, (a \u2294 b) \u2294 c = a \u2294 (b \u2294 c); join_absorptive : forall a b, a \u2294 (a \u2293 b) = a; join_idempotent : forall a, a \u2294 a = a*) }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 36
              }
            ]
          },
          "step": {
            "text": " intros.",
            "context": []
          },
          "n_step": 6,
          "goals": [
            "a, b: BinarySet\n\na = meet_BinarySet a b -> BinaryRel a b"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 77,
            "context": [
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryOrder : Order BinarySet := { ord := BinaryRel }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 10
              },
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryLattice : Lattice BinarySet := { meet := meet_BinarySet; join := join_BinarySet; (*meet_commutative : forall a b, a \u2293 b = b \u2293 a; meet_associative : forall a b c, (a \u2293 b) \u2293 c = a \u2293 (b \u2293 c); meet_absorptive : forall a b, a \u2293 (a \u2294 b) = a; meet_idempotent : forall a, a \u2293 a = a; join_commutative : forall a b, a \u2294 b = b \u2294 a; join_associative : forall a b c, (a \u2294 b) \u2294 c = a \u2294 (b \u2294 c); join_absorptive : forall a b, a \u2294 (a \u2293 b) = a; join_idempotent : forall a, a \u2294 a = a*) }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 36
              }
            ]
          },
          "step": {
            "text": " induction a; induction b; auto; unfold meet_BinarySet in H; inversion H;\n    try apply bot_rel; try apply top_rel.",
            "context": [
              {
                "type": "TermType.DEFINITION",
                "text": "Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | top => b | bottom => bottom end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 24
              },
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinaryRel : BinarySet -> BinarySet -> Prop := | bot_rel x : BinaryRel bottom x | top_rel x : BinaryRel x top.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 6
              }
            ]
          },
          "n_step": 7,
          "goals": [
            "a, b: BinarySet\nH: a = meet_BinarySet a b\n\nBinaryRel a b"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 77,
            "context": [
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryOrder : Order BinarySet := { ord := BinaryRel }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 10
              },
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryLattice : Lattice BinarySet := { meet := meet_BinarySet; join := join_BinarySet; (*meet_commutative : forall a b, a \u2293 b = b \u2293 a; meet_associative : forall a b c, (a \u2293 b) \u2293 c = a \u2293 (b \u2293 c); meet_absorptive : forall a b, a \u2293 (a \u2294 b) = a; meet_idempotent : forall a, a \u2293 a = a; join_commutative : forall a b, a \u2294 b = b \u2294 a; join_associative : forall a b c, (a \u2294 b) \u2294 c = a \u2294 (b \u2294 c); join_absorptive : forall a b, a \u2294 (a \u2293 b) = a; join_idempotent : forall a, a \u2294 a = a*) }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 36
              }
            ]
          },
          "step": {
            "text": "\nDefined.",
            "context": []
          },
          "n_step": 8,
          "goals": []
        }
      ]
    },
    {
      "theorem": {
        "type": "TermType.OBLIGATION",
        "text": "Next Obligation.",
        "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
        "module": [],
        "line": 83,
        "context": [
          {
            "type": "TermType.INSTANCE",
            "text": "Program Instance BinaryOrder : Order BinarySet := { ord := BinaryRel }.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 10
          },
          {
            "type": "TermType.INSTANCE",
            "text": "Program Instance BinaryLattice : Lattice BinarySet := { meet := meet_BinarySet; join := join_BinarySet; (*meet_commutative : forall a b, a \u2293 b = b \u2293 a; meet_associative : forall a b c, (a \u2293 b) \u2293 c = a \u2293 (b \u2293 c); meet_absorptive : forall a b, a \u2293 (a \u2294 b) = a; meet_idempotent : forall a, a \u2293 a = a; join_commutative : forall a b, a \u2294 b = b \u2294 a; join_associative : forall a b c, (a \u2294 b) \u2294 c = a \u2294 (b \u2294 c); join_absorptive : forall a b, a \u2294 (a \u2293 b) = a; join_idempotent : forall a, a \u2294 a = a*) }.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 36
          }
        ]
      },
      "steps": [
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 83,
            "context": [
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryOrder : Order BinarySet := { ord := BinaryRel }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 10
              },
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryLattice : Lattice BinarySet := { meet := meet_BinarySet; join := join_BinarySet; (*meet_commutative : forall a b, a \u2293 b = b \u2293 a; meet_associative : forall a b c, (a \u2293 b) \u2293 c = a \u2293 (b \u2293 c); meet_absorptive : forall a b, a \u2293 (a \u2294 b) = a; meet_idempotent : forall a, a \u2293 a = a; join_commutative : forall a b, a \u2294 b = b \u2294 a; join_associative : forall a b c, (a \u2294 b) \u2294 c = a \u2294 (b \u2294 c); join_absorptive : forall a b, a \u2294 (a \u2293 b) = a; join_idempotent : forall a, a \u2294 a = a*) }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 36
              }
            ]
          },
          "step": {
            "text": " Proof.",
            "context": []
          },
          "n_step": 1,
          "goals": [
            "a, b: BinarySet\n\nBinaryRel a b <-> b = join_BinarySet a b"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 83,
            "context": [
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryOrder : Order BinarySet := { ord := BinaryRel }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 10
              },
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryLattice : Lattice BinarySet := { meet := meet_BinarySet; join := join_BinarySet; (*meet_commutative : forall a b, a \u2293 b = b \u2293 a; meet_associative : forall a b c, (a \u2293 b) \u2293 c = a \u2293 (b \u2293 c); meet_absorptive : forall a b, a \u2293 (a \u2294 b) = a; meet_idempotent : forall a, a \u2293 a = a; join_commutative : forall a b, a \u2294 b = b \u2294 a; join_associative : forall a b c, (a \u2294 b) \u2294 c = a \u2294 (b \u2294 c); join_absorptive : forall a b, a \u2294 (a \u2293 b) = a; join_idempotent : forall a, a \u2294 a = a*) }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 36
              }
            ]
          },
          "step": {
            "text": "\n  split.",
            "context": []
          },
          "n_step": 2,
          "goals": [
            "a, b: BinarySet\n\nBinaryRel a b <-> b = join_BinarySet a b"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 83,
            "context": [
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryOrder : Order BinarySet := { ord := BinaryRel }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 10
              },
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryLattice : Lattice BinarySet := { meet := meet_BinarySet; join := join_BinarySet; (*meet_commutative : forall a b, a \u2293 b = b \u2293 a; meet_associative : forall a b c, (a \u2293 b) \u2293 c = a \u2293 (b \u2293 c); meet_absorptive : forall a b, a \u2293 (a \u2294 b) = a; meet_idempotent : forall a, a \u2293 a = a; join_commutative : forall a b, a \u2294 b = b \u2294 a; join_associative : forall a b c, (a \u2294 b) \u2294 c = a \u2294 (b \u2294 c); join_absorptive : forall a b, a \u2294 (a \u2293 b) = a; join_idempotent : forall a, a \u2294 a = a*) }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 36
              }
            ]
          },
          "step": {
            "text": "\n  -",
            "context": []
          },
          "n_step": 3,
          "goals": [
            "a, b: BinarySet\n\nBinaryRel a b -> b = join_BinarySet a b",
            "a, b: BinarySet\n\nb = join_BinarySet a b -> BinaryRel a b"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 83,
            "context": [
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryOrder : Order BinarySet := { ord := BinaryRel }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 10
              },
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryLattice : Lattice BinarySet := { meet := meet_BinarySet; join := join_BinarySet; (*meet_commutative : forall a b, a \u2293 b = b \u2293 a; meet_associative : forall a b c, (a \u2293 b) \u2293 c = a \u2293 (b \u2293 c); meet_absorptive : forall a b, a \u2293 (a \u2294 b) = a; meet_idempotent : forall a, a \u2293 a = a; join_commutative : forall a b, a \u2294 b = b \u2294 a; join_associative : forall a b c, (a \u2294 b) \u2294 c = a \u2294 (b \u2294 c); join_absorptive : forall a b, a \u2294 (a \u2293 b) = a; join_idempotent : forall a, a \u2294 a = a*) }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 36
              }
            ]
          },
          "step": {
            "text": " intros.",
            "context": []
          },
          "n_step": 4,
          "goals": [
            "a, b: BinarySet\n\nBinaryRel a b -> b = join_BinarySet a b"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 83,
            "context": [
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryOrder : Order BinarySet := { ord := BinaryRel }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 10
              },
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryLattice : Lattice BinarySet := { meet := meet_BinarySet; join := join_BinarySet; (*meet_commutative : forall a b, a \u2293 b = b \u2293 a; meet_associative : forall a b c, (a \u2293 b) \u2293 c = a \u2293 (b \u2293 c); meet_absorptive : forall a b, a \u2293 (a \u2294 b) = a; meet_idempotent : forall a, a \u2293 a = a; join_commutative : forall a b, a \u2294 b = b \u2294 a; join_associative : forall a b c, (a \u2294 b) \u2294 c = a \u2294 (b \u2294 c); join_absorptive : forall a b, a \u2294 (a \u2293 b) = a; join_idempotent : forall a, a \u2294 a = a*) }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 36
              }
            ]
          },
          "step": {
            "text": " induction a; induction b; auto; unfold join_BinarySet; inversion H.",
            "context": [
              {
                "type": "TermType.DEFINITION",
                "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 30
              }
            ]
          },
          "n_step": 5,
          "goals": [
            "a, b: BinarySet\nH: BinaryRel a b\n\nb = join_BinarySet a b"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 83,
            "context": [
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryOrder : Order BinarySet := { ord := BinaryRel }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 10
              },
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryLattice : Lattice BinarySet := { meet := meet_BinarySet; join := join_BinarySet; (*meet_commutative : forall a b, a \u2293 b = b \u2293 a; meet_associative : forall a b c, (a \u2293 b) \u2293 c = a \u2293 (b \u2293 c); meet_absorptive : forall a b, a \u2293 (a \u2294 b) = a; meet_idempotent : forall a, a \u2293 a = a; join_commutative : forall a b, a \u2294 b = b \u2294 a; join_associative : forall a b c, (a \u2294 b) \u2294 c = a \u2294 (b \u2294 c); join_absorptive : forall a b, a \u2294 (a \u2293 b) = a; join_idempotent : forall a, a \u2294 a = a*) }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 36
              }
            ]
          },
          "step": {
            "text": "\n  -",
            "context": []
          },
          "n_step": 6,
          "goals": []
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 83,
            "context": [
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryOrder : Order BinarySet := { ord := BinaryRel }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 10
              },
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryLattice : Lattice BinarySet := { meet := meet_BinarySet; join := join_BinarySet; (*meet_commutative : forall a b, a \u2293 b = b \u2293 a; meet_associative : forall a b c, (a \u2293 b) \u2293 c = a \u2293 (b \u2293 c); meet_absorptive : forall a b, a \u2293 (a \u2294 b) = a; meet_idempotent : forall a, a \u2293 a = a; join_commutative : forall a b, a \u2294 b = b \u2294 a; join_associative : forall a b c, (a \u2294 b) \u2294 c = a \u2294 (b \u2294 c); join_absorptive : forall a b, a \u2294 (a \u2293 b) = a; join_idempotent : forall a, a \u2294 a = a*) }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 36
              }
            ]
          },
          "step": {
            "text": " intros.",
            "context": []
          },
          "n_step": 7,
          "goals": [
            "a, b: BinarySet\n\nb = join_BinarySet a b -> BinaryRel a b"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 83,
            "context": [
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryOrder : Order BinarySet := { ord := BinaryRel }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 10
              },
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryLattice : Lattice BinarySet := { meet := meet_BinarySet; join := join_BinarySet; (*meet_commutative : forall a b, a \u2293 b = b \u2293 a; meet_associative : forall a b c, (a \u2293 b) \u2293 c = a \u2293 (b \u2293 c); meet_absorptive : forall a b, a \u2293 (a \u2294 b) = a; meet_idempotent : forall a, a \u2293 a = a; join_commutative : forall a b, a \u2294 b = b \u2294 a; join_associative : forall a b c, (a \u2294 b) \u2294 c = a \u2294 (b \u2294 c); join_absorptive : forall a b, a \u2294 (a \u2293 b) = a; join_idempotent : forall a, a \u2294 a = a*) }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 36
              }
            ]
          },
          "step": {
            "text": " induction a; induction b; auto; unfold join_BinarySet in H; inversion H;\n    try apply bot_rel; try apply top_rel.",
            "context": [
              {
                "type": "TermType.DEFINITION",
                "text": "Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet := match a with | bottom => b | top => top end.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 30
              },
              {
                "type": "TermType.INDUCTIVE",
                "text": "Inductive BinaryRel : BinarySet -> BinarySet -> Prop := | bot_rel x : BinaryRel bottom x | top_rel x : BinaryRel x top.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 6
              }
            ]
          },
          "n_step": 8,
          "goals": [
            "a, b: BinarySet\nH: b = join_BinarySet a b\n\nBinaryRel a b"
          ]
        },
        {
          "term": {
            "type": "TermType.OBLIGATION",
            "text": "Next Obligation.",
            "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "module": [],
            "line": 83,
            "context": [
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryOrder : Order BinarySet := { ord := BinaryRel }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 10
              },
              {
                "type": "TermType.INSTANCE",
                "text": "Program Instance BinaryLattice : Lattice BinarySet := { meet := meet_BinarySet; join := join_BinarySet; (*meet_commutative : forall a b, a \u2293 b = b \u2293 a; meet_associative : forall a b c, (a \u2293 b) \u2293 c = a \u2293 (b \u2293 c); meet_absorptive : forall a b, a \u2293 (a \u2294 b) = a; meet_idempotent : forall a, a \u2293 a = a; join_commutative : forall a b, a \u2294 b = b \u2294 a; join_associative : forall a b c, (a \u2294 b) \u2294 c = a \u2294 (b \u2294 c); join_absorptive : forall a b, a \u2294 (a \u2293 b) = a; join_idempotent : forall a, a \u2294 a = a*) }.",
                "file_path": "repos/yalhessi-verified-verifier/BinaryLattice.v",
                "module": [],
                "line": 36
              }
            ]
          },
          "step": {
            "text": "\nDefined.",
            "context": []
          },
          "n_step": 9,
          "goals": []
        }
      ]
    }
  ]
}