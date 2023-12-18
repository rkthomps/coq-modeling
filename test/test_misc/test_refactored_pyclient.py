import os
import shutil
import ipdb

from coqpyt.coq.proof_file import ProofFile
from coqpyt.coq.changes import CoqAddStep, CoqDeleteStep
from coqpyt.coq.exceptions import InvalidChangeException
from model_deployment.proof_manager import get_fresh_path

example_text = """\
Example test1: 1 + 1 = 2. reflexivity. Qed.

Example test2: 1 + 1 + 1= 3. rewrite test1. reflexivity. Qed.
"""

test_change_steps_expected = """\
Example test1: 1 + 1 = 2. Admitted.

Example test2: 1 + 1 + 1= 3. rewrite test1. reflexivity. Qed.
"""

example2_text = """\
Lemma add_0: forall n, n + 0 = n. 
Proof.
Admitted.
"""


def go_to_step(p: ProofFile, step_idx: int) -> None:
    while p.steps_taken < step_idx:
        p.exec(1)
    while step_idx < p.steps_taken:
        p.exec(-1)


def go_through_step(p: ProofFile, step_idx: int) -> None:
    while p.steps_taken < step_idx + 1:
        p.exec(1)
    while step_idx + 1 < p.steps_taken:
        p.exec(-1)


class TestCoqPytExample:
    @staticmethod
    def __get_file_contents(file_path: str) -> str:
        with open(file_path, "r") as fin:
            return fin.read()

    def test_change_steps(self) -> None:
        with ProofFile(self.file1_path) as proof_file:
            proof_file.run()
            proof_file.change_steps(
                [CoqDeleteStep(2), CoqDeleteStep(1), CoqAddStep(" Admitted.", 0)]
            )
            assert proof_file.is_valid
            assert test_change_steps_expected == self.__get_file_contents(
                self.file1_path
            )

            proof_file.change_steps(
                [
                    CoqDeleteStep(1),
                    CoqAddStep(" reflexivity.", 0),
                    CoqAddStep(" Qed.", 1),
                ]
            )
            assert proof_file.is_valid
            assert example_text == self.__get_file_contents(self.file1_path)

    def test_intros_vs_induction(self) -> None:
        with ProofFile(self.file2_path) as proof_file:
            proof_file.change_steps(
                [
                    CoqAddStep(" intros.", 1),
                ]
            )
            go_through_step(proof_file, 2)
            assert proof_file.current_goals is not None
            assert proof_file.current_goals.goals is not None
            assert len(proof_file.current_goals.goals.goals) == 1

            go_through_step(proof_file, 0)
            proof_file.change_steps(
                [
                    CoqDeleteStep(2),
                    CoqAddStep(" induction n.", 1),
                ]
            )

            go_through_step(proof_file, 2)
            assert proof_file.current_goals is not None
            assert proof_file.current_goals.goals is not None
            assert len(proof_file.current_goals.goals.goals) == 2

    @classmethod
    def setup_class(cls) -> None:
        cls.file1_path = get_fresh_path(".", "proof_ex_file.v")
        with open(cls.file1_path, "w") as fout:
            fout.write(example_text)

        cls.file2_path = get_fresh_path(".", "ex_file2.v")
        with open(cls.file2_path, "w") as fout:
            fout.write(example2_text)

    @classmethod
    def teardown_class(cls) -> None:
        if os.path.exists(cls.file1_path):
            os.remove(cls.file1_path)
        if os.path.exists(cls.file2_path):
            os.remove(cls.file2_path)
