from typing import Optional
import sys, os
import shutil
from pathlib import Path

import ipdb

from model_deployment.goal_comparer import (
    ParsedHyp,
    ParsedObligation,
    ParsedObligations,
    extract_body_from_step,
    compare_expressions_under_substitution,
)

from model_deployment.proof_manager import get_fresh_path, ProofManager

from coqpyt.coq.base_file import CoqFile
from coqpyt.coq.proof_file import ProofFile


class StrawHyp:
    def __init__(self, names: list[str], body: str) -> None:
        self.names = names
        self.body = body


class StrawOb:
    def __init__(self, imports: list[str], hyps: list[StrawHyp], goal: str) -> None:
        self.imports = imports
        self.hyps = hyps
        self.goal = goal

    @staticmethod
    def def_wrap(s: str, name: str) -> str:
        return f"Definition {name} := ({s})."

    def coq_str(self) -> str:
        import_str = "\n\n".join(self.imports)
        hyp_str = "\n\n".join(
            [self.def_wrap(h.body, "H" + str(i)) for i, h in enumerate(self.hyps)]
        )
        goal_str = self.def_wrap(self.goal, "G")
        return f"{import_str}\n\n{hyp_str}\n\n{goal_str}"

    def get_parsed(self) -> ParsedObligation:
        tmp_file = get_fresh_path(Path("."), "tmp.v")
        try:
            return self.__get_parsed(tmp_file)
        finally:
            if os.path.exists(tmp_file):
                os.remove(tmp_file)

    def __get_parsed(self, file: Path) -> ParsedObligation:
        with open(file, "w") as fout:
            fout.write(self.coq_str())
        parsed_hyps: list[ParsedHyp] = []
        with CoqFile(str(file.resolve())) as coq_file:
            for i, hyp in enumerate(self.hyps):
                step = coq_file.steps[len(self.imports) + i]
                hyp_ast = extract_body_from_step(step)
                parsed_hyps.append(ParsedHyp(hyp.names, hyp_ast, step.text))
            goal_def = coq_file.steps[len(self.imports) + len(self.hyps)]
            goal_ast = extract_body_from_step(goal_def)
        return ParsedObligation(parsed_hyps, goal_ast, goal_def.text)


test1_ob = StrawOb(
    imports=[],
    hyps=[
        StrawHyp(["H1"], "x1 = x3"),
        StrawHyp(["H2"], "x1 = x2"),
        StrawHyp(["H3"], "x1 = x2"),
    ],
    goal="x3 = x2",
)

test2_ob = StrawOb(
    imports=[],
    hyps=[
        StrawHyp(["H1"], "x1 = x3"),
        StrawHyp(["H2"], "x1 = x2"),
    ],
    goal="x3 = x2",
)

test3_ob = StrawOb(
    imports=[],
    hyps=[
        StrawHyp(["H1"], "x1 = x3"),
        StrawHyp(["H2"], "x1 = x2"),
        StrawHyp(["H3"], "x1 = x2"),
        StrawHyp(["H4"], "foo x1 x2"),
    ],
    goal="x3 = x2",
)

test4_ob = StrawOb(
    imports=[],
    hyps=[
        StrawHyp(["H1"], "x1 = x3"),
        StrawHyp(["H2"], "x1 = x2"),
        StrawHyp(["H3"], "x1 = x2"),
    ],
    goal="x3 = x2 + 1",
)

test_min1_ob = StrawOb(imports=["Require Import List."], hyps=[], goal="nil = 0 :: nil")

test_min2_ob = StrawOb(
    imports=["Require Import List."],
    hyps=[StrawHyp(["a"], "nat")],
    goal="nil = S a :: nil",
)

test_min3_ob = StrawOb(
    imports=["Require Import List."],
    hyps=[
        StrawHyp(["a"], "nat"),
        StrawHyp(["H"], "a :: nil <> nil"),
        StrawHyp(["x"], "nat"),
        StrawHyp(["H0"], "min nil = Some x"),
    ],
    goal="exists h : nat, min (a :: nil) = Some h",
)

test_min4_ob = StrawOb(
    imports=["Require Import List."],
    hyps=[
        StrawHyp(["a", "n"], "nat"),
        StrawHyp(["l"], "list nat"),
        StrawHyp(["H"], "a :: n :: l <> nil"),
        StrawHyp(["IHl"], "n :: l <> nil -> exists h : nat, min (n :: l) = Some h"),
    ],
    goal="exists h : nat, min (a :: n :: l) = Some h",
)


class TestGoalComparer:
    @classmethod
    def setup_class(cls) -> None:
        cls.o1 = test1_ob.get_parsed()
        cls.o2 = test2_ob.get_parsed()
        cls.o3 = test3_ob.get_parsed()
        cls.o4 = test4_ob.get_parsed()

        cls.min1 = test_min1_ob.get_parsed()
        cls.min2 = test_min2_ob.get_parsed()
        cls.min3 = test_min3_ob.get_parsed()
        cls.min4 = test_min4_ob.get_parsed()

    def test_equiv_goals(self) -> None:
        assert self.o1.as_hard_as(self.o2)
        assert self.o2.as_hard_as(self.o1)

    def test_harder_goals(self) -> None:
        assert not self.o3.as_hard_as(self.o1)
        assert not self.o3.as_hard_as(self.o2)
        assert self.o1.as_hard_as(self.o3)
        assert self.o2.as_hard_as(self.o3)

    def test_non_comparable_goals(self) -> None:
        assert not self.o4.as_hard_as(self.o3)
        assert not self.o3.as_hard_as(self.o4)
        assert not self.o4.as_hard_as(self.o1)
        assert not self.o1.as_hard_as(self.o4)
        assert not self.o4.as_hard_as(self.o2)
        assert not self.o2.as_hard_as(self.o4)

    def test_min_goals(self) -> None:
        obs1 = ParsedObligations([self.min1, self.min2, self.min3, self.min4])
        obs2 = ParsedObligations([self.min1, self.min2, self.min3, self.min4])
        assert obs1.as_hard_as(obs2)
        assert obs2.as_hard_as(obs1)

    def test_compare_expressions(self) -> None:
        # fmt: off
        expr1 = ['DefineBody', [], None, {'v': ['CNotation', None, [['InConstrEntry'], '_ = _'], [[{'v': ['CRef', {'v': ['Ser_Qualid', ['DirPath', []], ['Id', 't0']]}, None]}, {'v': ['CRef', {'v': ['Ser_Qualid', ['DirPath', []], ['Id', 't1']]}, None]}], [], [], []]]}, None]
        expr2 = ['DefineBody', [], None, {'v': ['CNotation', None, [['InConstrEntry'], '_ = _'], [[{'v': ['CRef', {'v': ['Ser_Qualid', ['DirPath', []], ['Id', 't0']]}, None]}, {'v': ['CRef', {'v': ['Ser_Qualid', ['DirPath', []], ['Id', 't1']]}, None]}], [], [], []]]}, None]
        one_to_two_mapping = {'G': 'G', 't1': 't1', 't2': 't2', 'R': 'R', 'H': None, 'G0': 'G0', 't0': 't0', 't3': None, 'T11': 'T11', 'T12': None, 'H4': None, 'H1': None, 'H0': None, 'H3': None, 'H2': None, 'H5': None, 'H6': None}
        two_avail_vars = {'H1', 't0', 'T12', 'H4', 'H3', 't1', 'G0', 'R', 'H2', 'H', 'G', 't2', 't3', 'H0', 'T11'}
        fresh_var_mapping: dict[str, str] = {}
        # fmt: on
        assert compare_expressions_under_substitution(
            expr1, expr2, one_to_two_mapping, two_avail_vars, fresh_var_mapping
        )

    @classmethod
    def teardown_class(cls) -> None:
        pass
