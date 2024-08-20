
Require Import RangoTest.ListDefs.


Module Test2.

Notation "x :: l" := (Test.cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := Test.nil.
Notation "[ x ; .. ; y ]" := (Test.cons x .. (Test.cons y Test.nil) .. ).

Notation "l1 ++ l2" := (Test.app l1 l2)
                       (at level 60, right associativity).
  
Theorem app_nil_r: forall {α : Type} (l : Test.list α),
  l ++ [] = l.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Theorem app_assoc: forall {α : Type} (l1 l2 l3 : Test.list α ),
  l1 ++ l2 ++ l3 = (l1 ++ l2) ++ l3.
  intros α l1 l2 l3. 
  induction l1.
  - reflexivity. 
  - simpl. rewrite IHl1. reflexivity.
Qed.


Theorem rev_app: forall {α : Type} (l1 l2: Test.list α),
  Test.rev l2 ++ Test.rev l1 = Test.rev (l1 ++ l2).
  intros α l1 l2.
  induction l1.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite <- IHl1. auto. rewrite app_assoc. 
    reflexivity.
Qed.

Theorem rev_involutive: forall {α: Type} (l: Test.list α),
    Test.rev (Test.rev l) = l.
Proof.
  intros α l.
  induction l.
  - reflexivity.
  - simpl. rewrite <- rev_app. rewrite IHl. simpl. 
    reflexivity.
Qed.

End Test2.


