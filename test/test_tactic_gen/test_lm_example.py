import os
import shutil
import ipdb
from test_utils.utils import (
    LIST_DEFS_DP,
    LIST_THMS_DP,
    TEST_MINI_DATASET_LOC,
    TEST_MINI_DATASET_SENTENCE_DB,
)

from premise_selection.premise_filter import (
    PremiseFilter,
    PremiseFilterConf,
    PROJ_THM_FILTER_CONF,
)
from data_management.sentence_db import SentenceDB
from data_management.splits import DATA_POINTS_NAME, REPOS_NAME
from data_management.dataset_file import DatasetFile
from tactic_gen.lm_example import (
    LmExample,
    GeneralFormatterConf,
    GeneralFormatter,
    formatter_conf_from_yaml,
    formatter_from_conf,
)

from test_utils.test_data_utils import setup_project_dataset


class TestLmExample:
    def examples_from_file(
        self, formatter: GeneralFormatter, dp: DatasetFile
    ) -> list[LmExample]:
        examples: list[LmExample] = []
        for proof_idx, proof in enumerate(dp.proofs):
            for step_idx, step in enumerate(proof.steps):
                examples.append(formatter.example_from_step(step_idx, proof_idx, dp))
        return examples

    def expected_num_examples(self, dp: DatasetFile) -> int:
        proj_thm_filter = PremiseFilter.from_conf(PROJ_THM_FILTER_CONF)
        num_examples = 0
        for proof in dp.proofs:
            num_examples += len(proof.steps)
        return num_examples

    def test_lemma_example(self):
        lm_conf = {
            "alias": "general",
            "premise_filter": {"known_filter": "proj-thm"},
            "premise": {
                "alias": "sparse",
                "kind": "tfidf",
                "context_format_alias": "basic",
                "premise_format_alias": "basic",
                "premise_filter": {"known_filter": "proj-thm"},
                "sentence_db_loc": TEST_MINI_DATASET_SENTENCE_DB,
            },
            "proof_ret": {
                "alias": "sparse",
                "kind": "tfidf",
                "max_examples": 20,
                "data_loc": TEST_MINI_DATASET_LOC,
                "sentence_db_loc": TEST_MINI_DATASET_SENTENCE_DB,
            },
            "num_premises": 50,
            "num_proofs": 20,
        }
        lm_formatter_conf = formatter_conf_from_yaml(lm_conf)
        lm_formatter = formatter_from_conf(lm_formatter_conf)
        for dp in [self.defs_dp, self.thms_dp]:
            for proof_idx, proof in enumerate(dp.proofs):
                for step_idx, step in enumerate(proof.steps):
                    example = lm_formatter.example_from_step(step_idx, proof_idx, dp)
                    assert example.proofs is not None
                    assert example.premises is not None
                    if 0 < len(step.goals):
                        assert proof_idx <= len(example.proofs)
                        assert proof_idx <= len(example.premises)
                    assert all(
                        proof.proof_text_to_string() not in p for p in example.proofs
                    )
                    assert all(
                        proof.theorem.term.text not in p for p in example.premises
                    )
                    assert isinstance(example, LmExample)

    @classmethod
    def setup_class(cls):
        setup_project_dataset()
        cls.sentence_db = SentenceDB.load(TEST_MINI_DATASET_SENTENCE_DB)
        cls.defs_dp = DatasetFile.load(
            TEST_MINI_DATASET_LOC / DATA_POINTS_NAME / LIST_DEFS_DP, cls.sentence_db
        )
        cls.thms_dp = DatasetFile.load(
            TEST_MINI_DATASET_LOC / DATA_POINTS_NAME / LIST_THMS_DP, cls.sentence_db
        )

    @classmethod
    def teardown_class(cls):
        cls.sentence_db.close()


if __name__ == "__main__":
    TestLmExample.setup_class()
    TestLmExample().test_lemma_example()
    TestLmExample.teardown_class()
