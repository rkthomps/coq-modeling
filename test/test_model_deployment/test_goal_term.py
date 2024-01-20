from model_deployment.goal_term import (
    term_dist,
    term_size,
    FixT,
    VarT,
    AppT,
    term_to_json,
)
from model_deployment.parse_goal_term import term_p
import ipdb


class TestGoalTerm:
    def test_goal_term1(self) -> None:
        assert term_dist(VarT("hi"), VarT("hi")) == 0

    def test_goal_term2(self) -> None:
        assert term_dist(VarT("hi"), VarT("bob")) == 1

    def test_term_dist1(self) -> None:
        term1 = term_p.parse("(a (1 2))")
        term2 = term_p.parse("(b (1 2))")
        assert term_dist(term1, term2) == 1

    def test_term_dist2(self) -> None:
        term1 = term_p.parse("(a (1 3))")
        term2 = term_p.parse("(b (1 2))")
        assert term_dist(term1, term2) == 2

    def test_term_dist3(self) -> None:
        term1 = term_p.parse("(a (1 3))")
        term2 = term_p.parse("(b (4 2))")
        assert term_dist(term1, term2) == 3

    def test_term_dist4(self) -> None:
        term1 = term_p.parse("(a (1 3) (4 5))")
        term2 = term_p.parse("(a (4 5) (1 3))")
        assert term_dist(term1, term2) == 1

    def test_term_dist5(self) -> None:
        term1 = term_p.parse("(a (1 3) (4 5) (9 9))")
        term2 = term_p.parse("(a (4 5) (1 3))")
        assert term_dist(term1, term2) == 3

    def test_term_size1(self) -> None:
        term1 = term_p.parse("(a (1 2))")
        assert term_size(term1) == 3

    def test_term_size2(self) -> None:
        term1 = term_p.parse("(a b c (1 2 (3 4 5)))")
        assert term_size(term1) == 8

    # def test_goal_term3(self) -> None:
    #     term1 = """forall _ : (eq 1 3), False"""
    #     term2 = """fix cat (a : nat) : nat := 1"""
