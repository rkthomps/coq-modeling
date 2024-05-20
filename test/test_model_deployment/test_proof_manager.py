

from pathlib import Path

from util.test_utils import build_mini_test_project, MINI_TEST_PROJET_LOC
from model_deployment.proof_manager import ProofManager 


class TestProofManager:
    TEST_IND_LOC = MINI_TEST_PROJET_LOC / "theories" / "Induction.v"

    @classmethod
    def setup_class(cls):
        build_mini_test_project()

    @classmethod
    def teardown_class(cls):
        pass

