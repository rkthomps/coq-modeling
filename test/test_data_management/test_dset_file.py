import os
import shutil
from pathlib import Path

from hypothesis import given, strategies as st

from data_management.create_file_data_point import get_data_point, get_switch_loc
from data_management.dataset_file import (
    DatasetFile,
    Proof,
    Term,
    FocusedStep,
    Sentence,
    Goal,
)
from data_management.sentence_db import SentenceDB
from coqpyt.coq.structs import TermType

from test_utils.utils import (
    build_test_project,
    get_test_sentence_db,
    TEST_TMP_LOC,
    LIST_DEFS_LOC,
    LIST_THMS_LOC,
    TEST_PROJET_LOC,
    SENTENCE_DB_LOC,
)


class TestDsetFile:
    def test_list_thms_dp(self):
        assert len(self.list_thms_dp.proofs) == 4

    def test_available_sentence(self):
        expected_in_file_name = Path(
            "/coq-dataset/repos/test-project/theories/ListThms.v"
        )
        expected_dep_name = Path("/coq-dataset/repos/test-project/theories/ListDefs.v")

        for p in self.list_thms_dp.in_file_avail_premises:
            assert p.file_path == str(expected_in_file_name)

        assert all(
            not p.file_path == str(expected_dep_name)
            for p in self.list_thms_dp.in_file_avail_premises
        )

        assert any(
            p.file_path == str(expected_dep_name)
            for p in self.list_thms_dp.out_of_file_avail_premises
        )

        assert all(
            not p.file_path == str(expected_in_file_name)
            for p in self.list_thms_dp.out_of_file_avail_premises
        )

    def test_load_save(self):
        save_loc = TEST_TMP_LOC / "list_thms_dp.json"
        self.list_thms_dp.save(save_loc, self.sentence_db, insert_allowed=False)
        load1 = DatasetFile.load(save_loc, self.sentence_db)
        os.remove(save_loc)
        self.list_thms_dp.save(save_loc, self.sentence_db, insert_allowed=True)
        load2 = DatasetFile.load(save_loc, self.sentence_db)
        new_sentence_db = SentenceDB.load(SENTENCE_DB_LOC)
        load3 = DatasetFile.load(save_loc, new_sentence_db)
        assert self.list_thms_dp == load1
        assert load1 == load2
        assert load2 == load3
        new_sentence_db.close()

    @classmethod
    def setup_class(cls) -> None:
        build_test_project()
        cls.sentence_db = get_test_sentence_db()
        cls.list_thms_dp = get_data_point(
            LIST_THMS_LOC,
            TEST_PROJET_LOC,
            cls.sentence_db,
            add_to_dataset=True,
            switch_loc=get_switch_loc(),
        )

    @classmethod
    def teardown_class(cls) -> None:
        cls.sentence_db.close()
        shutil.rmtree(TEST_TMP_LOC)
