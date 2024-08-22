import os
import shutil
import ipdb
from util.test_utils import (
    TEST_PROJET_LOC,
    LIST_DEFS_LOC,
    LIST_THMS_LOC,
    TEST_TMP_LOC,
    get_test_sentence_db,
)

from premise_selection.premise_filter import (
    PremiseFilter,
    PremiseFilterConf,
    PROJ_THM_FILTER_CONF,
)
from data_management.sentence_db import SentenceDB
from data_management.splits import DATA_POINTS_NAME, REPOS_NAME
from data_management.dataset_file import DatasetFile
from data_management.create_file_data_point import get_data_point, get_switch_loc
from tactic_gen.lm_example import (
    LmExample,
    GeneralFormatterConf,
    GeneralFormatter,
    formatter_conf_from_yaml,
    formatter_from_conf,
)


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
                "sentence_db_loc": self.sentence_db_loc,
            },
            "proof_ret": {
                "alias": "sparse",
                "kind": "tfidf",
                "max_examples": 20,
                "data_loc": self.test_data_loc,
                "sentence_db_loc": self.sentence_db_loc,
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
                    try:
                        assert proof_idx <= len(example.proofs)
                    except AssertionError:
                        ipdb.set_trace()
                    assert example.premises is not None
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
        cls.test_data_loc = TEST_TMP_LOC / "test-data"
        if cls.test_data_loc.exists():
            shutil.rmtree(cls.test_data_loc)

        os.makedirs(cls.test_data_loc / REPOS_NAME)
        os.makedirs(cls.test_data_loc / DATA_POINTS_NAME)
        cls.sentence_db_loc = cls.test_data_loc / "sentences.db"
        cls.sentence_db = SentenceDB.create(cls.sentence_db_loc)
        workspace_loc = cls.test_data_loc / REPOS_NAME / TEST_PROJET_LOC.name
        shutil.copytree(TEST_PROJET_LOC, workspace_loc)

        list_defs_loc = workspace_loc / (LIST_DEFS_LOC.relative_to(TEST_PROJET_LOC))
        list_thms_loc = workspace_loc / (LIST_DEFS_LOC.relative_to(TEST_PROJET_LOC))

        cls.defs_dp = get_data_point(
            list_defs_loc, workspace_loc, cls.sentence_db, True, get_switch_loc()
        )
        cls.thms_dp = get_data_point(
            list_thms_loc, workspace_loc, cls.sentence_db, True, get_switch_loc()
        )

        cls.defs_dp.save(
            cls.test_data_loc / DATA_POINTS_NAME / cls.defs_dp.dp_name,
            cls.sentence_db,
            insert_allowed=True,
        )
        cls.thms_dp.save(
            cls.test_data_loc / DATA_POINTS_NAME / cls.thms_dp.dp_name,
            cls.sentence_db,
            insert_allowed=True,
        )

    @classmethod
    def teardown_class(cls):
        cls.sentence_db.close()
        shutil.rmtree(TEST_TMP_LOC)


if __name__ == "__main__":
    TestLmExample.setup_class()
    TestLmExample().test_lemma_example()
    TestLmExample.teardown_class()
