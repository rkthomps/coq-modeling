from model_deployment.goal_term import (
    AppT,
    VarT,
    ProdT,
    ParamT,
    FunT,
    FixT,
)
from model_deployment.parse_goal_term import term_p, app_p
import ipdb


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


    def test_failure_1(self) -> None:
        test_str = "forall _ : (eq 1 3), False"
        test_res = ProdT(
            [ParamT("_", AppT(VarT("eq"), [VarT("1"), VarT("3")]))], VarT("False")
        )
        assert term_p.parse(test_str) == test_res

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
