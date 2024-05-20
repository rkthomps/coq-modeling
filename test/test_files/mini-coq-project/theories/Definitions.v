

Require Import Coq.Strings.String.


Module Lambda.


Inductive Expr := 
    | Var (v : string)
    | App (e1: Expr) (e2: Expr) 
    | Abs (param: string) (body: Expr).


Inductive value: Expr -> Prop := 
    | v_abs: forall p b, value (Abs p b).


Declare Custom Entry lambda.
Notation "<{ e }>" := e (e custom lambda at level 99).
Notation "( x )" := x (in custom lambda, x at level 99).
Notation "x" := x (in custom lambda at level 0, x constr at level 0).
Notation "\ x , y" := (Abs x y) (in custom lambda at level 90, x at level 99,
                     y custom lambda at level 99,
                     left associativity).
Notation "x y" := (App x y) (in custom lambda at level 1, left associativity).
Coercion Var: string >-> Expr.

Definition x: string := "x".
Definition y: string := "y".
Definition apple: string := "apple".
Definition bananna: string := "bananna".

Definition e_id := <{ \x, x }>.

Unset Printing Notations.
Print e_id. 


Fixpoint subst (before: string) (after: Expr) (e: Expr): Expr :=
    match e with
    | Var v => if (before =? v)%string then after else (Var v)
    | App e1 e2 => App (subst before after e1) (subst before after e2)
    | Abs p b => if (p =? before)%string then Abs p b else Abs p (subst before after b)
    end.


Definition e_apple_bananna := <{ (\x, (\y, y)) apple bananna }>.

Example subst_ab: subst apple y e_apple_bananna = <{ (\x, (\y, y)) y bananna }>. reflexivity. Qed.

Definition reduce_beta (e: Expr): Expr := 
    match e with
    | App (Abs p b) e2 => subst p e2 b
    | _ => e
    end.


Example id_value: value e_id. apply v_abs. Qed. 

End Lambda.