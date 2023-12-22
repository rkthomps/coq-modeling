import os
import shutil
import ipdb

from coqpyt.coq.proof_file import ProofFile
from coqpyt.coq.changes import CoqAddStep, CoqDeleteStep
from coqpyt.coq.exceptions import InvalidChangeException
from model_deployment.proof_manager import get_fresh_path

example2_text = """\
Lemma add_0: forall n, n + 0 = n. 
Proof.
Admitted.
"""


def get_fresh_path(dirname: str, fresh_base: str) -> str:
    name = fresh_base
    while os.path.exists(os.path.join(dirname, name)):
        name = "_" + name
    return os.path.join(dirname, name)


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

            # go_through_step(proof_file, 0)
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
        cls.file2_path = get_fresh_path(".", "ex_file2.v")
        with open(cls.file2_path, "w") as fout:
            fout.write(example2_text)

    @classmethod
    def teardown_class(cls) -> None:
        if os.path.exists(cls.file2_path):
            os.remove(cls.file2_path)
