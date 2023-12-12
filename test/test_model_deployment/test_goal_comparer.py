from typing import Optional
import sys, os
import shutil

import ipdb

from model_deployment.goal_comparer import (
    ParsedHyp,
    ParsedObligation,
    extract_body_from_step,
    compare_expressions_under_substitution,
)

from tactic_gen.lm_example import BasicFormatter
from tactic_gen.n_step_sampler import OneStepSampler
from model_deployment.proof_manager import get_fresh_path, ProofManager

from coqpyt.coq.base_file import CoqFile
from coqpyt.coq.proof_file import ProofFile


test_file_1 = """\
Definition def0 := (x1 = x3).

Definition def1 := (x1 = x2).

Definition def2 := (x1 = x2).

Definition def3 := (x3 = x2).
"""

# Same as 1
test_file_2 = """\
Definition def0 := (x1 = x3).

Definition def1 := (x1 = x2).

Definition def2 := (x3 = x2).
"""

# Easier than 1, 2
test_file_3 = """\
Definition def0 := (x1 = x3).

Definition def1 := (x1 = x2).

Definition def2 := (x1 = x2).

Definition def3 := (foo x1 x2).

Definition def3 := (x3 = x2).
"""

# Not comparable to prior 1, 2, 3
test_file_4 = """\
Definition def0 := (x1 = x3).

Definition def1 := (x1 = x2).

Definition def2 := (x1 = x2).

Definition def3 := (x3 = x2 + 1).
"""


class TestGoalComparer:
    def test_equiv_goals(self) -> None:
        assert self.file1_ob.as_hard_as(self.file2_ob)
        assert self.file2_ob.as_hard_as(self.file1_ob)

    def test_equiv_exprs(self) -> None:
        avail_vars1: dict[str, Optional[str]] = {
            v: None for v in self.file1_ob.get_all_vars()
        }
        avail_vars3 = set(self.file3_ob.get_all_vars())
        assert compare_expressions_under_substitution(
            self.file1_ob.hyps[0].ast,
            self.file3_ob.hyps[0].ast,
            avail_vars1,
            avail_vars3,
            {},
        )
        assert compare_expressions_under_substitution(
            self.file1_ob.hyps[1].ast,
            self.file3_ob.hyps[1].ast,
            avail_vars1,
            avail_vars3,
            {},
        )
        assert compare_expressions_under_substitution(
            self.file1_ob.hyps[1].ast,
            self.file3_ob.hyps[1].ast,
            avail_vars1,
            avail_vars3,
            {},
        )
        assert compare_expressions_under_substitution(
            self.file1_ob.hyps[2].ast,
            self.file3_ob.hyps[2].ast,
            avail_vars1,
            avail_vars3,
            {},
        )
        avail_vars1: dict[str, Optional[str]] = {
            v: None for v in self.file1_ob.get_all_vars()
        }
        avail_vars3 = set(self.file3_ob.get_all_vars())
        assert not compare_expressions_under_substitution(
            self.file1_ob.hyps[0].ast,
            self.file3_ob.hyps[3].ast,
            avail_vars1,
            avail_vars3,
            {},
        )
        avail_vars1: dict[str, Optional[str]] = {
            v: None for v in self.file1_ob.get_all_vars()
        }
        avail_vars3 = set(self.file3_ob.get_all_vars())
        assert not compare_expressions_under_substitution(
            self.file1_ob.hyps[1].ast,
            self.file3_ob.hyps[3].ast,
            avail_vars1,
            avail_vars3,
            {},
        )
        avail_vars1: dict[str, Optional[str]] = {
            v: None for v in self.file1_ob.get_all_vars()
        }
        avail_vars3 = set(self.file3_ob.get_all_vars())
        assert not compare_expressions_under_substitution(
            self.file1_ob.hyps[2].ast,
            self.file3_ob.hyps[3].ast,
            avail_vars1,
            avail_vars3,
            {},
        )

    def test_harder_goals(self) -> None:
        assert not self.file3_ob.as_hard_as(self.file1_ob)
        assert not self.file3_ob.as_hard_as(self.file2_ob)
        assert self.file1_ob.as_hard_as(self.file3_ob)
        assert self.file2_ob.as_hard_as(self.file3_ob)

    def test_non_comparable_goals(self) -> None:
        assert not self.file4_ob.as_hard_as(self.file3_ob)
        assert not self.file3_ob.as_hard_as(self.file4_ob)
        assert not self.file4_ob.as_hard_as(self.file1_ob)
        assert not self.file1_ob.as_hard_as(self.file4_ob)
        assert not self.file4_ob.as_hard_as(self.file2_ob)
        assert not self.file2_ob.as_hard_as(self.file4_ob)

    def skip_test_inversion(self) -> None:
        basic_formatter = BasicFormatter(OneStepSampler(), False, None)
        with ProofFile(self.test_inversion1_loc) as proof_file1:
            proof_file1.run()
            pm1 = ProofManager(
                self.test_inversion1_loc,
                proof_file1,
                len(proof_file1.steps) - 2,
                basic_formatter,
            )
            current_goals = proof_file1.current_goals
            assert current_goals is not None
            pg1 = pm1.get_parsed_goals("", current_goals)

        with ProofFile(self.test_inversion2_loc) as proof_file2:
            proof_file2.run()
            pm2 = ProofManager(
                self.test_inversion2_loc,
                proof_file2,
                len(proof_file2.steps) - 2,
                basic_formatter,
            )
            current_goals = proof_file2.current_goals
            assert current_goals is not None
            pg2 = pm2.get_parsed_goals("", current_goals)

        assert len(pg1.obligations) == 1
        assert len(pg2.obligations) == 1
        assert pg1.obligations[0].as_hard_as(pg2.obligations[0])
        assert pg2.obligations[0].as_hard_as(pg1.obligations[0])

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
    def __get_basic_goal(cls, file_loc: str, hyp_prefix: str) -> ParsedObligation:
        hyps: list[ParsedHyp] = []
        with CoqFile(file_loc) as coq_file:
            for i, step in enumerate(coq_file.steps[:-1]):
                hyp_name = f"{hyp_prefix}{str(i)}"
                parsed_hyp = ParsedHyp([hyp_name], extract_body_from_step(step))
                hyps.append(parsed_hyp)
            goal = ParsedObligation(hyps, extract_body_from_step(coq_file.steps[-1]))
        return goal

    @classmethod
    def setup_class(cls) -> None:
        cls.file1_loc = get_fresh_path(".", "file1.v")
        with open(cls.file1_loc, "w") as fout:
            fout.write(test_file_1)
        cls.file1_ob = cls.__get_basic_goal(cls.file1_loc, "H1")

        cls.file2_loc = get_fresh_path(".", "file2.v")
        with open(cls.file2_loc, "w") as fout:
            fout.write(test_file_2)
        cls.file2_ob = cls.__get_basic_goal(cls.file2_loc, "H2")

        cls.file3_loc = get_fresh_path(".", "file3.v")
        with open(cls.file3_loc, "w") as fout:
            fout.write(test_file_3)
        cls.file3_ob = cls.__get_basic_goal(cls.file3_loc, "H3")

        cls.file4_loc = get_fresh_path(".", "file4.v")
        with open(cls.file4_loc, "w") as fout:
            fout.write(test_file_4)
        cls.file4_ob = cls.__get_basic_goal(cls.file4_loc, "H4")

        cls.test_files_loc = os.path.join("test", "test_files")
        if not os.path.exists(cls.test_files_loc):
            raise ValueError(
                f"{cls.test_files_loc} does not exsist. You should be in the root dir of the project."
            )
        cls.test_inversion1_loc = os.path.join(cls.test_files_loc, "inversion_1.v")
        cls.test_inversion2_loc = os.path.join(cls.test_files_loc, "inversion_2.v")

    @classmethod
    def teardown_class(cls) -> None:
        os.remove(cls.file1_loc)
        os.remove(cls.file2_loc)
        os.remove(cls.file3_loc)
        os.remove(cls.file4_loc)
