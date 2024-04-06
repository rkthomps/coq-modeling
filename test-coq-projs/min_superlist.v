

Require Export List.
Require Export Nat. 
Require Export Bool.

Fixpoint remove_nth_error {X : Type} (l : list X) (n : nat) : option (list X) :=
    (** Remove the nth element in the list *)
    match l with
    | nil => None 
    | h :: l' => match n with
        | O => Some l' 
        | S n' => match (remove_nth_error l' n') with
            | Some l_remove => Some (h :: l_remove)
            | None => None
            end
        end
    end.

Fixpoint insert_nth_error {X : Type} (l : list X) (n : nat) (a : X): option (list X) :=
    (** Insert a at the nth element in the list. Push previous down the list.*)
    match l, n with 
    | _, O => Some (a :: l)
    | nil, (S n') => None
    | h :: l', (S n') => match (insert_nth_error l' n' a) with
        | Some l_insert => Some (h :: l_insert)
        | None => None 
        end
    end.

Definition swap {X : Type} (l : list X) (k : nat): option (list X) := 
    (** Swaps the head of the list with the element at position k.*)
    match l, (nth_error l k) with
    | _, None => None
    | nil, _ => None
    | h :: l', (Some a) => match (remove_nth_error l' (k - 1)) with
        | Some shortend_list => match (insert_nth_error shortend_list (k - 1) h) with
            | Some swaped_list => Some (a :: swaped_list)
            | None => None
            end
        | None => None
        end
    end.
    
Example test_swap_1: (swap ((1 :: (2 :: (3 :: nil)))) 1) = Some (2 :: (1 :: (3 :: nil))).
Proof. reflexivity. Qed.

Example test_swap_2: (swap (1 :: (2 :: 3 :: nil)) 3) = None.
Proof. reflexivity. Qed.

Example test_swap_3: (swap (1 :: (2 :: (3 :: (4 :: nil)))) 2) = Some (3 :: (2 :: (1 :: (4 :: nil)))).
Proof. reflexivity. Qed.

Fixpoint reverse {X : Type} (l : list X) : list X :=
    match l with 
    | nil => nil
    | h :: l' => (reverse l') ++ (h :: nil)
    end.

Example test_reverse_1: (reverse (1 :: (2 :: (3 :: nil))) = (3 :: (2 :: (1 :: nil)))).
Proof. reflexivity. Qed.

Example test_reverse_2: (@reverse (list nat) nil) = nil. 
Proof. reflexivity. Qed.

Fixpoint bubble_down_small (l : list nat): list nat :=
    (** Place the smallest element in the list at the beginning of the list. 
        Ensure the set of elements in the list is preserved. 
        Smallest is determined by f. 
        f returns true when its first argument is less than its second. Else false *)
    match l with
    | h :: l' => match bubble_down_small l' with
        | h' :: l'' => if (ltb h' h) then
            h' :: h :: l'' else
            h :: h' :: l''
        | nil => h :: nil
        end
    | nil => nil 
    end. 

Fixpoint bubble_down_large (l : list nat): list nat :=
    (** Place the smallest element in the list at the beginning of the list. 
        Ensure the set of elements in the list is preserved. 
        Smallest is determined by f. 
        f returns true when its first argument is less than its second. Else false *)
    match l with
    | h :: l' => match bubble_down_large l' with
        | h' :: l'' => if h <? h' then
            h' :: h :: l'' else
            h :: h' :: l''
        | nil => h :: nil
        end
    | nil => nil 
    end. 

Lemma leb_refl: forall (n : nat), (n <=? n) = true.
Proof. 
    intros n. induction n as [|n' IHn'].
    - reflexivity.
    - simpl. rewrite IHn'. reflexivity.
Qed.

Lemma succ_preserves_lt: forall (n1 n2 : nat),
    (n1 <? n2) = ((S n1) <? (S n2)).
Proof.
    intros n1. destruct n1 as [|n1'].
    - intros n2. destruct n2 eqn:E. 
      + reflexivity.
      + reflexivity.
    - intros n2. destruct n2 eqn:E.
      + reflexivity.
      + reflexivity.
  Qed.

Lemma if_ltb_then_leb: forall (n1 n2 : nat),
    (n1 <? n2 = true) -> (n1 <=? n2 = true).
Proof.
    intros n1. induction n1 as [|n1' IHn1'].
    - reflexivity. 
    - simpl. destruct n2 eqn:E.
      + intros H2. discriminate H2. 
      + intros H2.  rewrite succ_preserves_lt in H2.
        apply IHn1'. apply H2. 
Qed.

Example nth_test_1: 
    (nth 1 (1 :: 2 :: nil) 0) = 2.
Proof. reflexivity. Qed.

Example nth_test_2: 
    (nth 3 (1 :: 2 :: nil) 0) = 0.
Proof. reflexivity. Qed.


Definition nth_is_some (n: option nat): Prop :=
    match n with
    | Some n' => True
    | None => False
    end. 

Definition le_when_defined (n1 n2: option nat): Prop :=
    match n1 with
    | None => True
    | Some n1' => match n2 with
        | None => True
        | Some n2' => (n1' <=? n2') = true
        end
    end.

Theorem nth_error_nil_none: forall {X : Type} (n : nat), 
    @nth_error X nil n = None.
Proof. 
    intros X n. destruct n as [|n'].
    - reflexivity.
    - reflexivity.
Qed.

Lemma leb_sym_forward: forall (n1 n2 : nat),
    (n1 <=? n2 = true) -> (n2 <? n1 = false).
Proof. 
    intros n1. induction n1 as [|n1' IHn1'].
    - reflexivity.
    - simpl. destruct n2 eqn:E.
      + intros H. discriminate H. 
      + apply IHn1' with (n2:=n). 
  Qed.

Fixpoint max (l : (list nat)) : option nat := 
    match l with
    | nil => None
    | h :: tl => match (max tl) with
        | None => Some h 
        | Some m => if (m <? h) then (Some h) else (Some m)
        end
    end.

Fixpoint min (l : (list nat)) : option nat := 
    match l with
    | nil => None
    | h :: tl => match (min tl) with
        | None => Some h 
        | Some m => if (h <? m) then (Some h) else (Some m)
        end
    end.

Lemma min_rewrite: forall (n : nat) (l : (list nat)), 
    min (n :: l) = match (min l) with
        | None => Some n
        | Some m => if (n <? m) then (Some n) else (Some m)
    end.
Proof. 
    Admitted.

Lemma leb_sym_backward: forall (n1 n2 : nat),
    (n1 <? n2 = false) -> (n2 <=? n1 = true).
Proof.
    intros n1. induction n1 as [|n1' IHn1'].
    - intros n2. intros H. destruct n2.
      + reflexivity. 
      + discriminate H. 
    - destruct n2 eqn:E.
      + reflexivity. 
      + simpl. apply IHn1'.
  Qed.

Lemma lt_leb_sym: forall (n1 n2 : nat),
    ((n2 <=? n1) = (negb (n1 <? n2))).
Proof.
    intros n1. induction n1 as [|n1' IHn1'].
    - intros n2. destruct n2 eqn:E. 
      + reflexivity.
      + reflexivity.
    - intros n2. destruct n2 eqn:E.
      + reflexivity.
      + simpl. rewrite IHn1'. rewrite succ_preserves_lt.
        reflexivity.
Qed.

(*
There are two cases to consider: l is empty and l is nonempty. If l is empty, there is a contradiction with the assumption. If l is nonempty, the min of the tail is either Some h' or None. If the min of the tail is Some h', the min depends on whether h' is smaller than the head. If the min of the tail is None, then the min is the head. 
*)
Lemma exists_min: forall (l : (list nat)), 
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
Qed.


Fixpoint in_list (l : (list nat)) (n : nat) : Prop :=
    match l with
    | nil => False
    | h :: l' => if h =? n then True else in_list l' n
    end.

Lemma rewrite_in_list: forall (l : (list nat)) (h n : nat),
    in_list (h :: l) n = if h =? n then True else in_list l n. 
Proof. reflexivity. Qed.


Lemma if_eqb_then_eq: forall (n1 n2 : nat),
    (n1 =? n2) = true <-> n1 = n2.
Proof.
    - intros n1. induction n1 as [|n1' IHn1'].
      + intros n2. destruct n2 eqn:E.
        * split. 
          -- reflexivity.  
          -- reflexivity.
        * split. 
          -- intros H. discriminate H.
          -- intros H. discriminate H.
      + intros n2. destruct n2 eqn:E.
        * split.
          -- intros H. discriminate H.
          -- intros H. discriminate H.
        * split. 
          -- intros H. simpl in H. apply IHn1' in H. rewrite H. reflexivity. 
          -- intros H. simpl. rewrite IHn1'. injection H as H.  rewrite H. reflexivity.
Qed.

Lemma rewrite_negb_true:
    forall (b : bool), (negb b) = true <-> b = false. 
Proof.
    intros b. destruct b. 
    - split. 
      + intros H. discriminate H. 
      + intros H. discriminate H. 
    - split.
      + intros H. reflexivity.
      + intros H. reflexivity. 
  Qed. 

(* Theorem min_superlist_less: forall (l : (list nat)) (n1 n2 x1 x2: nat),
    min (n2 :: l) = Some x1 -> 
    min (n1 :: n2 :: l) = Some x2 ->
    x2 <=? x1 = true. 
Proof. 
    intros. rewrite min_rewrite in H0. rewrite H in H0.  
    destruct (n1 <? x1) eqn:E.
    - injection H0 as H0. rewrite H0 in E. <prove> *)

Theorem min_superlist_less: forall (l : (list nat)) (n1 n2 x1 x2: nat),
    min (n2 :: l) = Some x1 -> 
    min (n1 :: n2 :: l) = Some x2 ->
    x2 <=? x1 = true. 
Proof. 
    intros. rewrite min_rewrite in H0. rewrite H in H0.  
    destruct (n1 <? x1) eqn:E.
    - injection H0 as H0. rewrite H0 in E. apply if_ltb_then_leb.  
      apply E. 
    - injection H0 as H0. rewrite H0. apply leb_refl. 
Qed. 
