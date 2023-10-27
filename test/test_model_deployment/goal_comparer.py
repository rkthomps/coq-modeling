import sys, os
import unittest
import pdb

from model_deployment.goal_comparer import (
    ParsedHyp,
    ParsedObligation,
    ParsedObligations,
    extract_body_from_step,
)
from model_deployment.proof_manager import get_fresh_path

from coqlspclient.coq_file import CoqFile


test_file_1 = """\
Definition def0 := (x1 = x3).

Definition def1 := (x1 = x2).

Definition def2 := (x1 = x2).

Definition def3 := (x3 = x2).
"""

test_file_2 = """\
Definition def0 := (x1 = x3).

Definition def1 := (x1 = x2).

Definition def2 := (x3 = x2).
"""


class GoalComparerTestCase(unittest.TestCase):
    def test_redundant_hyps(self) -> None:
        with CoqFile(self.file1_loc) as coq_file:
            hyp1 = ParsedHyp(["H1"], extract_body_from_step(coq_file.steps[0]))
            hyp2 = ParsedHyp(["H2"], extract_body_from_step(coq_file.steps[1]))
            hyp3 = ParsedHyp(["H3"], extract_body_from_step(coq_file.steps[2]))
            goal_body = extract_body_from_step(coq_file.steps[3])
            goal1 = ParsedObligation([hyp1, hyp2, hyp3], goal_body)

        with CoqFile(self.file2_loc) as coq_file:
            hyp1 = ParsedHyp(["H4"], extract_body_from_step(coq_file.steps[0]))
            hyp2 = ParsedHyp(["H5"], extract_body_from_step(coq_file.steps[1]))
            goal_body = extract_body_from_step(coq_file.steps[2])
            goal2 = ParsedObligation([hyp1, hyp2], goal_body)

        self.assertEqual(goal2.as_hard_as(goal1), True)
        self.assertEqual(goal1.as_hard_as(goal2), True)

    def setUp(self) -> None:
        self.file1_loc = get_fresh_path(".", "file1.v")
        with open(self.file1_loc, "w") as fout:
            fout.write(test_file_1)
        self.file2_loc = get_fresh_path(".", "file2.v")
        with open(self.file2_loc, "w") as fout:
            fout.write(test_file_2)

    def tearDown(self) -> None:
        os.remove(self.file1_loc)
        os.remove(self.file2_loc)
