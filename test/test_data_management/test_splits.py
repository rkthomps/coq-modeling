import os
import pdb
from pathlib import Path

from data_management.splits import DataSplit, Project, FileInfo
from data_management.sentence_db import SentenceDB
import pytest


class TestSplits:
    @pytest.mark.skip("Test need's to be updated.")
    def test_partition_mini_dataset(self) -> None:
        ds = DataSplit.create(self.data_path, self.sentence_db, time_sorted=True)
        file_info1 = FileInfo(
            "yalhessi-verified-verifier-BinaryLattice.v",
            "repos/yalhessi-verified-verifier/BinaryLattice.v",
            "repos/yalhessi-verified-verifier",
            "repos/yalhessi-verified-verifier",
        )
        file_info2 = FileInfo(
            "yalhessi-verified-verifier-BoundedLattice.v",
            "repos/yalhessi-verified-verifier/BoundedLattice.v",
            "repos/yalhessi-verified-verifier",
            "repos/yalhessi-verified-verifier",
        )
        file_info3 = FileInfo(
            "yalhessi-verified-verifier-Maps.v",
            "repos/yalhessi-verified-verifier/Maps.v",
            "repos/yalhessi-verified-verifier",
            "repos/yalhessi-verified-verifier",
        )
        exp_train_project = Project(
            "yalhessi-verified-verifier",
            [file_info1, file_info2, file_info3],
        )

        expected_ds = DataSplit([exp_train_project], [], [])
        ds.train_projects[0].files.sort(key=lambda f: f.dp_name)
        assert ds == expected_ds

    @classmethod
    def setup_class(cls) -> None:
        sentence_db_loc = Path("./sentences.db")
        cls.sentence_db = SentenceDB.load(sentence_db_loc)
        cls.data_path = Path("test/test_files/coq-mini-dataset")
        if not os.path.exists(cls.data_path):
            raise FileNotFoundError(
                f"{cls.data_path} not found. Run tests from root project dir."
            )
