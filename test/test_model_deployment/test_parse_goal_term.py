from model_deployment.goal_term import (
    AppT,
    VarT,
    ProdT,
    ParamT,
    FunT,
    FixT,
    LetT,
    TupleT,
    TupleTypeT,
)
from model_deployment.parse_goal_term import term_p, app_p, term_p_var
import ipdb

test_str_7 = """\
(fun h : nat =>
 eq
   ((fix min (l0 : list nat) : option nat :=
       match l0 with
       | nil => None
       | cons h0 tl =>
           match min tl with
           | Some m =>
               if
                match m with
                | 0 => false
                | S m' =>
                    (fix leb (n m0 : nat) {struct n} : bool :=
                       match n with
                       | 0 => true
                       | S n' =>
                           match m0 with
                           | 0 => false
                           | S m'0 => leb n' m'0
                           end
                       end) h0 m'
                end
               then Some h0
               else Some m
           | None => Some h0
           end
       end) l) (Some h))
"""


class TestTermCompare:
    def test_assoc(self) -> None:
        str1 = "a b"
        res1 = app_p.parse(str1)
        assert res1 == AppT(VarT("a"), [VarT("b")])
        str2 = "a b c"
        res2 = app_p.parse(str2)
        assert res2 == AppT(VarT("a"), [VarT("b"), VarT("c")])

    def test_app(self) -> None:
        str1 = "(a (1 3) (4 5) (9 9))"

    def test_let(self) -> None:
        test_str = "let (x, _) := p in x"
        res = term_p.parse(test_str)
        assert res == LetT(TupleT([VarT("x"), VarT("_")]), VarT("p"), VarT("x"))

    def test_tuple(self) -> None:
        test_str = "(a, b)"
        res = TupleT([VarT("a"), VarT("b")])
        assert res == term_p.parse(test_str)

    def test_prod(self) -> None:
        test_str = "fun Y : X * Z => x"
        res = term_p.parse(test_str)
        assert res == FunT([ParamT("Y", TupleTypeT([VarT("X"), VarT("Z")]))], VarT("x"))

    def test_failure_1(self) -> None:
        test_str = "forall _ : (eq 1 3), False"
        test_res = ProdT(
            [ParamT("_", AppT(VarT("eq"), [VarT("1"), VarT("3")]))], VarT("False")
        )
        assert term_p.parse(test_str) == test_res

    def test_failure_1_paren(self) -> None:
        test_str = "(forall _ : (eq 1 3), False)"
        test_res = ProdT(
            [ParamT("_", AppT(VarT("eq"), [VarT("1"), VarT("3")]))], VarT("False")
        )
        assert term_p_var.parse(test_str) == test_res

    def test_failure_1_simpl(self) -> None:
        test_str = "(forall _ : True, False)"
        test_res = ProdT([ParamT("_", VarT("True"))], VarT("False"))
        assert term_p_var.parse(test_str) == test_res

    def test_failure_2(self) -> None:
        # test_str = "forall (a : A) (s : forall _ : A, bool), sumbool (eq (s a) true) (forall _ : eq (s a) true, False)"
        test_str = "a 1 (forall _ : True, False)"
        test_res = AppT(
            VarT("a"), [VarT("1"), ProdT([ParamT("_", VarT("True"))], VarT("False"))]
        )
        assert term_p.parse(test_str) == test_res

    def test_failure_3(self) -> None:
        # test_str = "forall (x : X) (f : forall _ : X, X) (_ : forall (x0 y : X) (_ : le x0 y), le (f x0) (f y)), le (f x) (lfp (fun Y : X => join (f Y) x))"
        test_str = "fun Y : X => join (f Y) x"
        test_res = FunT(
            [ParamT("Y", VarT("X"))],
            AppT(VarT("join"), [AppT(VarT("f"), [VarT("Y")]), VarT("x")]),
        )
        res_act = term_p.parse(test_str)
        assert test_res == res_act

    def test_failure_4(self) -> None:
        test_str = "App.le"
        test_res = VarT("App.le")
        assert test_res == term_p.parse(test_str)

    def test_failure_5(self) -> None:
        test_str = "y'"
        test_res = VarT("y'")
        assert test_res == term_p.parse(test_str)

    def test_failure_6(self) -> None:
        test_str = "fix cat (a : nat) : nat := 1"
        test_res = FixT("cat", [ParamT("a", VarT("nat"))], VarT("nat"), VarT("1"))
        assert test_res == term_p.parse(test_str)

    def test_failure_7(self) -> None:
        term_p.parse(test_str_7)

    def test_failure_8(self) -> None:
        #         test_str = """\
        # forall (A : Type) (P : forall _ : A, Type) (f : forall (_ : E.t) (_ : A), A)
        # (initial : A) (set : S.t)
        # (_ : forall (x : E.t) (acc : A) (_ : P acc), P (f x acc))
        # (_ : P initial), P (S.fold f set initial)"""
        test_str = """forall (f : forall (_ : E.t), A) (initial : A), P"""
        term_p.parse(test_str)

    def test_failure_9(self) -> None:
        test_str = """((let (compare0, _, _) := C in compare0) x x)"""
        term_p.parse(test_str)

    def test_funky_symbol(self) -> None:
        test_str = "Σ"
        test_res = VarT("Σ")
        assert term_p.parse(test_str) == test_res
