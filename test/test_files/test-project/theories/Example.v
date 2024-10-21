Require Import PeanoNat.

Inductive MyList := 
  | MyNil : MyList
  | MyCons : nat -> MyList -> MyList. 

  
Fixpoint MyLength (l : MyList) : nat :=
  match l with
  | MyNil => 0
  | MyCons h tl => 1 + MyLength tl
  end.


Fixpoint MyIns (n : nat) (l : MyList): MyList :=
  match l with
    | MyNil => MyCons n MyNil
    | MyCons h tl => 
      if (n <=? h) 
        then MyCons n (MyCons h tl)
        else MyCons h (MyIns n tl)
  end.
  
Theorem InsLength : forall (n : nat) (l : MyList),
  MyLength (MyIns n l) = 1 + MyLength l.
Proof. 
  intros. 
  induction l. 
  - reflexivity.
  - simpl. destruct (n <=? n0).
    + reflexivity. 
    + simpl. rewrite IHl. reflexivity.
Qed.



(* 
rango finds:

Proof.
  intros. induction l as [ | m l'].
  - reflexivity.
  - simpl. destruct (n <=? m).
    + simpl. reflexivity.
    + simpl. rewrite IHl'. reflexivity.
 *)