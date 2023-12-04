import os
import shutil
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


class TestCoqPytExample:
    @staticmethod
    def __get_file_contents(file_path: str) -> str:
        with open(file_path, "r") as fin:
            return fin.read()

    def test_change_steps(self) -> None:
        with ProofFile(self.proof_file_path) as proof_file:
            proof_file.run()
            proof_file.change_steps(
                [CoqDeleteStep(2), CoqDeleteStep(1), CoqAddStep(" Admitted.", 0)]
            )
            assert proof_file.is_valid
            assert test_change_steps_expected == self.__get_file_contents(
                self.proof_file_path
            )

            proof_file.change_steps(
                [
                    CoqDeleteStep(1),
                    CoqAddStep(" reflexivity.", 0),
                    CoqAddStep(" Qed.", 1),
                ]
            )
            assert proof_file.is_valid
            assert example_text == self.__get_file_contents(self.proof_file_path)

    @classmethod
    def setup_class(cls) -> None:
        cls.file_path = get_fresh_path(".", "ex_file.v")
        cls.proof_file_path = get_fresh_path(".", "proof_ex_file.v")
        with open(cls.file_path, "w") as fout:
            fout.write(example_text)
        shutil.copy(cls.file_path, cls.proof_file_path)

    @classmethod
    def teardown_class(cls) -> None:
        if os.path.exists(cls.file_path):
            os.remove(cls.file_path)
        if os.path.exists(cls.proof_file_path):
            os.remove(cls.proof_file_path)
