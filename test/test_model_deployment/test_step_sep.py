import os
import random
from data_management.dataset_file import Proof, DatasetFile
from data_management.splits import DATA_POINTS_NAME
from model_deployment.step_separator import separate_steps


class TestStepSep:
    N_PROOFS = 1000
    RAW_DATA_LOC = "/data/benchmarks/coq-dataset"

    def test_proof_splitting(self) -> None:
        for proof in self.proofs:
            expected = [s.step.text for s in proof.steps]
            actual = separate_steps("".join(expected))
            assert expected == actual

    @classmethod
    def setup_class(cls) -> None:
        cls.proofs: list[Proof] = []
        dp_loc = os.path.join(cls.RAW_DATA_LOC, DATA_POINTS_NAME)
        names = os.listdir(dp_loc)
        random.shuffle(names)
        for dp_name in names:
            dp_obj_loc = os.path.join(dp_loc, dp_name)
            dp_obj = DatasetFile.from_directory(dp_obj_loc)
            for proof in dp_obj.proofs:
                cls.proofs.append(proof)
                if len(cls.proofs) == cls.N_PROOFS:
                    return

    @classmethod
    def teardown_class(cls) -> None:
        pass
