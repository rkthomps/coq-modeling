from pathlib import Path
from model_deployment.fast_client import FastLspClient, ClientWrapper


class TestFastClient:
    def test_fast_client(self):
        steps = self.wrapper.write_and_get_steps(TEST_CASE)
        assert "".join([s.text for s in steps]) == TEST_CASE

    @classmethod
    def teardown_class(cls):
        cls.wrapper.close()

    @classmethod
    def setup_class(cls):
        cur_path = Path(".").resolve()
        uri = f"file://{cur_path}"
        test_file_path = cur_path / "test_file.v"
        file_uri = f"file://{test_file_path}"
        fast_client = FastLspClient(uri)
        cls.wrapper = ClientWrapper(fast_client, file_uri)


TEST_CASE = r"""\
(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
From mathcomp Require Import path choice fintype tuple finset bigop order.
From mathcomp Require Import ssralg ssrint ssrnum rat.

From CoqEAL Require Import hrel param refinements pos.

(******************************************************************************)
(* Non-normalized rational numbers refines SSReflects rational numbers (rat)  *)
(*                                                                            *)
(* rational == Type of non normalized rational numbers                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import GRing.Theory Order.Theory Num.Theory Refinements.Op.

(*************************************************************)
(* PART I: Defining datastructures and programming with them *)
(*************************************************************)
Section Q.

Variable Z P N : Type.

(* Generic definition of rationals *)
Definition Q := (Z * P)%type.

(* Definition of operators on Q Z *)
Section Q_ops.

Local Open Scope computable_scope.

Context `{zero_of Z, one_of Z, add_of Z, opp_of Z, mul_of Z, eq_of Z, leq_of Z,
          lt_of Z}.
Context `{one_of P, sub_of P, add_of P, mul_of P, eq_of P, leq_of P, lt_of P}.
Context `{cast_of P Z, cast_of Z P}.
Context `{spec_of Z int, spec_of P pos, spec_of N nat}.

#[export] Instance zeroQ : zero_of Q := (0, 1).
#[export] Instance oneQ  : one_of Q  := (1, 1).
#[export] Instance addQ  : add_of Q  := fun x y =>
  (x.1 * cast y.2 + y.1 * cast x.2, x.2 * y.2).
#[export] Instance mulQ  : mul_of Q  := fun x y => (x.1 * y.1, x.2 * y.2).
#[export] Instance oppQ  : opp_of Q  := fun x   => (- x.1, x.2).
#[export] Instance eqQ   : eq_of Q   :=
  fun x y => (x.1 * cast y.2 == y.1 * cast x.2).
#[export] Instance leqQ  : leq_of Q  :=
  fun x y => (x.1 * cast y.2 <= y.1 * cast x.2).
#[export] Instance ltQ   : lt_of Q   :=
  fun x y => (x.1 * cast y.2 < y.1 * cast x.2).
#[export] Instance invQ : inv_of Q   := fun x   =>
  if      (x.1 == 0)%C   then 0
  else if (0 < x.1)      then (cast x.2, cast x.1)
                         else (- (cast x.2), cast (- x.1)).
#[export] Instance subQ : sub_of Q   := fun x y => (x + - y).
#[export] Instance divQ : div_of Q   := fun x y => (x * y^-1).
#[export] Instance expQnat : exp_of Q N := fun x n => iter (spec n) (mulQ x) 1.
#[export] Instance specQ : spec_of Q rat :=
  fun q => (spec q.1)%:~R / (cast (spec q.2 : pos))%:R.

(* Embedding from Z to Q *)
#[export] Instance cast_ZQ : cast_of Z Q := fun x => (x, 1).
#[export] Instance cast_PQ : cast_of P Q := fun x => cast (cast x : Z).

End Q_ops.
End Q.

Parametricity zeroQ.
Parametricity oneQ.
Parametricity addQ.
Parametricity mulQ.
Parametricity oppQ.
Parametricity eqQ.
Parametricity leqQ.
Parametricity ltQ.
Parametricity invQ.
Parametricity subQ.
Parametricity divQ.
Definition expQnat' := Eval compute in expQnat.
Parametricity expQnat'.
Realizer expQnat as expQnat_R := expQnat'_R.
Parametricity cast_ZQ.
Parametricity cast_PQ.

Arguments specQ / _ _ _ _ _ : assert.

(***********************************************************)
(* PART II: Proving the properties of the previous objects *)
(***********************************************************)
Section Qint.

Instance zero_int : zero_of int     := 0%R.
Instance one_int  : one_of int      := 1%R.
Instance add_int  : add_of int      := +%R.
Instance opp_int  : opp_of int      := -%R.
Instance mul_int  : mul_of int      := *%R.
Instance eq_int   : eq_of int       := eqtype.eq_op.
Instance leq_int  : leq_of int      := Num.le.
Instance lt_int   : lt_of int       := Num.lt.
Instance spec_int : spec_of int int := spec_id.

Instance cast_pos_int : cast_of pos int := pos_to_int.
Instance cast_int_pos : cast_of int pos := int_to_pos.
Instance spec_pos     : spec_of pos pos := spec_id.

Instance spec_nat : spec_of nat nat := spec_id.

Local Notation Qint := (Q int pos).

(* rat_to_Qint = repr *) (* Qint_to_rat = \pi_rat *)
Lemma absz_denq_gt0 r : (0 < `|denq r|)%N.
Proof. by rewrite absz_gt0 denq_eq0. Qed.

Definition rat_to_Qint (r : rat) : Qint := (numq r, pos_of (absz_denq_gt0 r)).
Definition Qint_to_rat (r : Qint) : rat := (r.1%:Q / (val r.2)%:Q).

Lemma Qrat_to_intK : cancel rat_to_Qint Qint_to_rat.
Proof. by move=> x; rewrite /Qint_to_rat /= absz_denq divq_num_den. Qed.

Local Open Scope rel_scope.

Definition Rrat : rat -> Q int pos -> Type := fun_hrel Qint_to_rat.

Instance Rrat_spec : refines (Rrat ==> Logic.eq) spec_id spec.
Proof. by rewrite refinesE=> _ x <-. Qed.

Lemma RratE (x : rat) (a : Qint) :
  refines Rrat x a -> x = a.1%:~R / (val a.2)%:~R.
Proof with eauto using divq_num_den.
move=> /=.
move=>?.
done."""
