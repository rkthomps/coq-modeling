import os
import shutil
import unittest
import pdb

from coqpyt.coq.proof_file import ProofFile
from coqpyt.coq.changes import CoqAddStep, CoqDeleteStep
from model_deployment.proof_manager import get_fresh_path

example_text = """\
Example test1: 1 + 1 = 2. reflexivity. Qed.

Example test2: 1 + 1 + 1= 3. rewrite test1. reflexivity. Qed.
"""

test_change_steps_expected = """\
Example test1: 1 + 1 = 2. Admitted.

Example test2: 1 + 1 + 1= 3. rewrite test1. reflexivity. Qed.
"""


class TestCoqPytExample(unittest.TestCase):
    @staticmethod
    def __get_file_contents(file_path: str) -> str:
        with open(file_path, "r") as fin:
            return fin.read()

    def test_change_steps(self) -> None:
        with ProofFile(self.proof_file_path) as proof_file:
            proof_file.change_steps(
                [CoqDeleteStep(2), CoqDeleteStep(1), CoqAddStep(" Admitted.", 0)]
            )
            self.assertTrue(proof_file.is_valid)
            self.assertEqual(
                test_change_steps_expected,
                self.__get_file_contents(self.proof_file_path),
            )
            proof_file.change_steps(
                [
                    CoqDeleteStep(1),
                    CoqAddStep(" reflexivity.", 0),
                    CoqAddStep(" Qed.", 1),
                ]
            )
            self.assertTrue(proof_file.is_valid)
            self.assertEqual(
                example_text, self.__get_file_contents(self.proof_file_path)
            )

    def setUp(self) -> None:
        self.file_path = get_fresh_path(".", "ex_file.v")
        self.proof_file_path = get_fresh_path(".", "proof_ex_file.v")
        with open(self.file_path, "w") as fout:
            fout.write(example_text)
        shutil.copy(self.file_path, self.proof_file_path)

    def tearDown(self) -> None:
        if os.path.exists(self.file_path):
            os.remove(self.file_path)
        if os.path.exists(self.proof_file_path):
            os.remove(self.proof_file_path)
