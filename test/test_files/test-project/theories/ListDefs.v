

Module Test.

Inductive list (α : Type): Type := 
  | nil 
  | cons (n : α) (l : list α).

Arguments nil {α}.
Arguments cons {α}.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) .. ).

                
Fixpoint app {α : Type} (l1 l2 : list α): list α :=  
  match l1 with
    | nil       => l2
    | h :: t    => h :: (app t l2)
  end.

Notation "l1 ++ l2" := (app l1 l2)
                       (at level 60, right associativity).

Fixpoint rev {α : Type} (l : list α): list α := 
  match l with
    | nil       => nil 
    | h :: t    => (rev t) ++ [h]
  end.


Fixpoint len {α : Type} (l : list α): nat := 
  match l with
    | nil => 0
    | h :: t => 1 + len t
  end.


Theorem app_len_plus: forall {α : Type} (l1 l2: list α),
  len (l1 ++ l2) = len l1 + len l2.
Proof.
  intros α l1 l2.
  induction l1.
  - reflexivity. 
  - simpl. rewrite IHl1. reflexivity.
Qed.

End Test.