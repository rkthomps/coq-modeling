import shutil
from util.test_utils import (
    TEST_PROJET_LOC,
    LIST_DEFS_LOC,
    LIST_THMS_LOC,
    TEST_TMP_LOC,
    get_test_sentence_db,
)

from data_management.create_file_data_point import get_data_point, get_switch_loc


class TestLemmaExample:

    def test_lemma_example(self):
        pass

    @classmethod
    def setup_class(cls):
        cls.sentence_db = get_test_sentence_db()
        cls.defs_dp = get_data_point(
            LIST_DEFS_LOC, TEST_PROJET_LOC, cls.sentence_db, True, get_switch_loc()
        )
        cls.thms_dp = get_data_point(
            LIST_THMS_LOC, TEST_PROJET_LOC, cls.sentence_db, True, get_switch_loc()
        )

    @classmethod
    def teardown_class(cls):
        shutil.rmtree(TEST_TMP_LOC)
