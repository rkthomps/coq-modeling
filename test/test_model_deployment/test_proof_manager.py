import os
import unittest

from data_management.create_lm_dataset import LmExampleConfig
from model_deployment.proof_manager import ProofManager, get_fresh_path
from coqpyt.coq.proof_file import ProofFile

example_text = """\
Example test1: 1 + 1 = 2. reflexivity. Qed.

Example test2: 1 + 1 + 1= 3. rewrite test1. reflexivity. Qed.
"""

test_change_steps_expected = """\
Example test1: 1 + 1 = 2. Admitted.

Example test2: 1 + 1 + 1= 3. rewrite test1. reflexivity. Qed.
"""


class TestProofManager(unittest.TestCase):
    @staticmethod
    def __get_file_contents(file_path: str) -> str:
        with open(file_path, "r") as fin:
            return fin.read()

    def test_proof_manager(self) -> None:
        with ProofFile(self.example_loc) as proof_file:
            proof_point = 0
            with ProofManager(
                self.example_loc, proof_file, proof_point, LmExampleConfig.void_config()
            ) as pm:
                self.assertTrue(pm.proof_file.is_valid)
                self.assertEqual(
                    test_change_steps_expected,
                    self.__get_file_contents(self.example_loc),
                )
            self.assertEqual(example_text, self.__get_file_contents(self.example_loc))

    def setUp(self) -> None:
        self.example_loc = get_fresh_path(".", "ex1.v")
        with open(self.example_loc, "w") as fout:
            fout.write(example_text)

    def tearDown(self) -> None:
        if os.path.exists(self.example_loc):
            os.remove(self.example_loc)
