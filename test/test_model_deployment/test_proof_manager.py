import os

from data_management.splits import FileInfo, Split
from tactic_gen.lm_example import BasicFormatter
from tactic_gen.n_step_sampler import OneStepSampler
from model_deployment.step_separator import separate_steps
from model_deployment.proof_manager import ProofManager, get_fresh_path
from coqpyt.coq.proof_file import ProofFile
import ipdb


example_text = """\
Example test1: 1 + 1 = 2. reflexivity. Qed.

Example test2: 1 + 1 + 1= 3. rewrite test1. reflexivity. Qed.
"""

empty_expected = """\
Example test1: 1 + 1 = 2.
Admitted.

Example test2: 1 + 1 + 1= 3. rewrite test1. reflexivity. Qed.
"""

change_empty_expeced = empty_expected

change_simpl_expected = """\
Example test1: 1 + 1 = 2. simpl.
Admitted.

Example test2: 1 + 1 + 1= 3. rewrite test1. reflexivity. Qed.
"""

change_refl_expected = """\
Example test1: 1 + 1 = 2. reflexivity.
Admitted.

Example test2: 1 + 1 + 1= 3. rewrite test1. reflexivity. Qed.
"""


class TestProofManager:
    @staticmethod
    def __get_file_contents(file_path: str) -> str:
        with open(file_path, "r") as fin:
            return fin.read()

    def test_proof_manager(self) -> None:
        file_info = FileInfo.incomplete_from_file(self.example_loc)
        split = Split.TRAIN
        data_loc = os.path.abspath(".")
        with ProofFile(self.example_loc) as proof_file:
            proof_point = 0
            with ProofManager(
                self.example_loc,
                proof_file,
                proof_point,
                BasicFormatter(OneStepSampler(), False, None),
                file_info,
                split,
                data_loc,
            ) as pm:
                assert pm.proof_file.is_valid
                assert empty_expected == self.__get_file_contents(self.example_loc)

                # pm.set_proof_file(separate_steps(""))
                # assert change_empty_expeced == self.__get_file_contents(
                #     self.example_loc
                # )

                pm.set_proof_file(separate_steps(" simpl."))
                assert change_simpl_expected == self.__get_file_contents(
                    self.example_loc
                )

                pm.set_proof_file(separate_steps(" reflexivity."))
                assert change_refl_expected == self.__get_file_contents(
                    self.example_loc
                )
            assert example_text == self.__get_file_contents(self.example_loc)

    @classmethod
    def setup_class(cls) -> None:
        cls.example_loc = get_fresh_path(".", "ex1.v")
        with open(cls.example_loc, "w") as fout:
            fout.write(example_text)

    @classmethod
    def teardown_class(cls) -> None:
        if os.path.exists(cls.example_loc):
            os.remove(cls.example_loc)
