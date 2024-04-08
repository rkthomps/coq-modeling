import os

from data_management.sentence_db import SentenceDB
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
        # Previous teste was outdated
        pass

    @classmethod
    def setup_class(cls) -> None:
        cls.example_loc = get_fresh_path(".", "ex1.v")
        sentence_db_loc = "./sentences.db"
        if not os.path.exists(sentence_db_loc):
            raise ValueError(
                "Sentences db doesn't exists. Expected it to be at ./sentences.db"
            )
        cls.sentence_db = SentenceDB.load(sentence_db_loc)

        with open(cls.example_loc, "w") as fout:
            fout.write(example_text)

    @classmethod
    def teardown_class(cls) -> None:
        if os.path.exists(cls.example_loc):
            os.remove(cls.example_loc)
