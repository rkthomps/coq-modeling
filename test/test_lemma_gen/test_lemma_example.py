import shutil
from test_utils.utils import (
    TEST_PROJET_LOC,
    LIST_DEFS_LOC,
    LIST_THMS_LOC,
    TEST_TMP_LOC,
    TEST_MINI_DATASET_SENTENCE_DB,
    TEST_MINI_DATASET_LOC,
    LIST_DEFS_DP,
    LIST_THMS_DP,
    get_test_sentence_db,
)
from test_utils.test_data_utils import setup_project_dataset

from premise_selection.premise_filter import (
    PremiseFilter,
    PremiseFilterConf,
    PROJ_THM_FILTER_CONF,
)
from lemma_gen.lemma_example import LemmaFormatterConf, LemmaFormatter, LemmaExample
from data_management.splits import DATA_POINTS_NAME
from data_management.dataset_file import DatasetFile
from data_management.sentence_db import SentenceDB
from data_management.create_file_data_point import get_data_point, get_switch_loc


class TestLemmaExample:
    def examples_from_file(
        self, formatter: LemmaFormatter, dp: DatasetFile
    ) -> list[LemmaExample]:
        examples: list[LemmaExample] = []
        for proof in dp.proofs:
            for step_idx, step in enumerate(proof.steps):
                examples.extend(formatter.examples_from_step(step_idx, proof, dp))
        return examples

    def expected_num_examples(self, dp: DatasetFile) -> int:
        proj_thm_filter = PremiseFilter.from_conf(PROJ_THM_FILTER_CONF)
        num_examples = 0
        for proof in dp.proofs:
            for step in proof.steps:
                filter_result = proj_thm_filter.get_pos_and_avail_premises(
                    step, proof, dp
                )
                num_examples += len(filter_result.pos_premises)
        return num_examples

    def example_no_leak(self, example: LemmaExample):
        if example.relevant_lemmas is None:
            return True
        for lemma in example.relevant_lemmas:
            if example.target in lemma:
                return False
        return True

    def test_lemma_example(self):
        lemma_conf = {
            "premise_filter": {"known_filter": "proj-thm"},
            "premise": {
                "alias": "sparse",
                "kind": "tfidf",
                "context_format_alias": "basic",
                "premise_format_alias": "basic",
                "sentence_db_loc": TEST_MINI_DATASET_SENTENCE_DB,
                "premise_filter": {"known_filter": "proj-thm"},
            },
            "max_num_premises": 50,
        }
        lemma_formatter_conf = LemmaFormatterConf.from_yaml(lemma_conf)
        lemma_formatter = LemmaFormatter.from_conf(lemma_formatter_conf)
        for dp in [self.defs_dp, self.thms_dp]:
            examples = self.examples_from_file(lemma_formatter, dp)
            assert len(examples) == self.expected_num_examples(dp)
            for example in examples:
                assert self.example_no_leak(example)

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
    TestLemmaExample.setup_class()
    TestLemmaExample().test_lemma_example()
    TestLemmaExample.teardown_class()
