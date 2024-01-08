import os
import random
from data_management.dataset_file import Proof, DatasetFile
from data_management.splits import DATA_POINTS_NAME
from model_deployment.step_separator import separate_steps
from util.util import get_basic_logger


_logger = get_basic_logger(__name__)

unit1 = """
Proof.
Proof.
  induction n.
  -\
"""


class TestStepSep:
    RAW_DATA_LOC = "test/test_files/coq-mini-dataset"

    def test_proof_splitting(self) -> None:
        num_steps_tested = 0
        for proof in self.proofs:
            for i in range(len(proof.steps)):
                for j in range(i + 1, len(proof.steps)):
                    expected = [s.step.text for s in proof.steps[i : (j + 1)]]
                    actual = separate_steps("".join(expected))
                    assert expected == actual
                    num_steps_tested += 1
        # _logger.error(f"Tested {num_steps_tested} steps.")
        # assert False

    def test_proof_split_unit1(self) -> None:
        expected = ["\nProof.", "\nProof.", "\n  induction n.", "\n  -"]
        actual = separate_steps(unit1)
        assert expected == actual

    @classmethod
    def setup_class(cls) -> None:
        cls.max_num_proofs = 1000
        cls.proofs: list[Proof] = []
        if not os.path.exists(cls.RAW_DATA_LOC):
            raise FileNotFoundError(
                f"Could not find {cls.RAW_DATA_LOC}. Perhaps you're not in the root project folder."
            )
        dp_loc = os.path.join(cls.RAW_DATA_LOC, DATA_POINTS_NAME)
        names = os.listdir(dp_loc)
        for dp_name in names:
            dp_obj_loc = os.path.join(dp_loc, dp_name)
            dp_obj = DatasetFile.from_directory(dp_obj_loc)
            for proof in dp_obj.proofs:
                cls.proofs.append(proof)

    @classmethod
    def teardown_class(cls) -> None:
        pass
