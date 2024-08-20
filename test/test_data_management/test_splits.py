import os
import pdb
import shutil
from pathlib import Path


from data_management.create_file_data_point import DATASET_PREFIX

from data_management.dataset_file import DatasetFile, dataset_file_from_project
from data_management.sentence_db import SentenceDB
from data_management.splits import (
    DataSplit,
    Split,
    FileInfo,
    DATA_POINTS_NAME,
    REPOS_NAME,
    PredefinedSplitConfig,
)
from data_management.sentence_db import SentenceDB
from hypothesis import strategies as st

from util.test_utils import TEST_FILES_LOC

from hypothesis import given


class TestSplits:

    def __get_thms(
        self,
        data_split: DataSplit,
        split: Split,
        data_loc: Path,
        sentence_db: SentenceDB,
    ) -> set[str]:
        match split:
            case Split.TRAIN:
                split_files = data_split.train_files
            case Split.VAL:
                split_files = data_split.val_files
            case Split.TEST:
                split_files = data_split.test_files
        dps = [f.get_dp(data_loc, sentence_db) for f in split_files]
        split_thms = set()
        for dp in dps:
            for proof in dp.proofs:
                split_thms.add(proof.theorem.term.text)
        return split_thms

    def __get_dp_thms(self, data_point: DatasetFile) -> set[str]:
        thms = set()
        for proof in data_point.proofs:
            thms.add(proof.theorem.term.text)
        return thms

    def test_create_predefined_data_split(self):
        config = PredefinedSplitConfig(
            [self.data_loc / REPOS_NAME / p for p in self.test_projects],
            [self.data_loc / REPOS_NAME / p for p in self.val_projects],
        )
        split = DataSplit.create(config, self.data_loc, self.sentence_db)

        # Files are in expected splits (by repo name)
        assert all(
            [Path(t.repository).name in self.test_projects for t in split.test_files]
        )
        assert all(
            [Path(t.repository).name in self.val_projects for t in split.val_files]
        )
        assert all(
            [
                f.get_dp(self.data_loc, self.sentence_db) in self.test_files
                for f in split.test_files
            ]
        )

        # Files are in expected splits (by file equality)
        assert all(
            [
                f.get_dp(self.data_loc, self.sentence_db) in self.val_files
                for f in split.val_files
            ]
        )
        assert all(
            [
                f.get_dp(self.data_loc, self.sentence_db) in self.train_files
                for f in split.train_files
            ]
        )

        # All testing files are present
        assert len(split.test_files) == len(self.test_files)
        assert len(split.test_files) == len(self.test_projects) * self.files_per_project

        # Splits have disjoint sets of theorems
        train_thms = self.__get_thms(
            split, Split.TRAIN, self.data_loc, self.sentence_db
        )
        val_thms = self.__get_thms(split, Split.VAL, self.data_loc, self.sentence_db)
        test_thms = self.__get_thms(split, Split.TEST, self.data_loc, self.sentence_db)
        assert train_thms.isdisjoint(val_thms)
        assert train_thms.isdisjoint(test_thms)
        assert val_thms.isdisjoint(test_thms)

        # If a file is missing, then it shares a theorem with another split
        for file in self.train_files:
            if not file.dp_name in [f.dp_name for f in split.train_files]:
                assert not self.__get_dp_thms(file).isdisjoint(val_thms | test_thms)

        for file in self.val_files:
            if not file.dp_name in [f.dp_name for f in split.val_files]:
                assert not self.__get_dp_thms(file).isdisjoint(test_thms)

    @staticmethod
    def create_test_data_points(
        projects: list[str],
        files_per_project: int,
        data_loc: Path,
        sentence_db_loc: Path,
    ):
        dp_names: set[str] = set()
        sentence_db = SentenceDB.create(sentence_db_loc)
        os.makedirs(data_loc / DATA_POINTS_NAME, exist_ok=True)
        for project in projects:
            os.makedirs(data_loc / REPOS_NAME / project, exist_ok=True)
            project_data_gen = dataset_file_from_project(str(DATASET_PREFIX / project))
            project_files = [
                project_data_gen.example() for _ in range(files_per_project)
            ]

            for p in project_files:
                while p.dp_name in dp_names:
                    p.file_context.file += ".v"

                dp_names.add(p.dp_name)
                p.save(data_loc / DATA_POINTS_NAME / p.dp_name, sentence_db, True)

    @staticmethod
    def load_files(data_loc: Path, sentence_db: SentenceDB) -> list[DatasetFile]:
        files: list[DatasetFile] = []
        for dp_name in os.listdir(data_loc / DATA_POINTS_NAME):
            files.append(
                DatasetFile.load(data_loc / DATA_POINTS_NAME / dp_name, sentence_db)
            )
        return files

    @classmethod
    def setup_class(cls):
        cls.test_projects = ["foo1", "foo2", "foo3", "foo4", "foo5", "foo6"]
        cls.val_projects = ["bar1", "bar2", "bar3", "bar4", "bar5", "bar6"]
        all_projects = (
            cls.test_projects
            + cls.val_projects
            + ["baz1", "baz2", "baz3", "baz4", "baz5", "baz6"]
        )
        cls.data_loc = TEST_FILES_LOC / "test-data"
        cls.sentence_db_loc = cls.data_loc / "sentences.db"

        cls.files_per_project = 30

        data_points_exists = (cls.data_loc / DATA_POINTS_NAME).exists()
        repos_exists = (cls.data_loc / REPOS_NAME).exists()

        if not (data_points_exists and repos_exists):
            if cls.data_loc.exists():
                shutil.rmtree(cls.data_loc)
            os.makedirs(cls.data_loc, exist_ok=True)
            cls.create_test_data_points(
                all_projects, cls.files_per_project, cls.data_loc, cls.sentence_db_loc
            )
        else:
            if (
                len(list((cls.data_loc / DATA_POINTS_NAME).iterdir()))
                != len(all_projects) * cls.files_per_project
            ):
                shutil.rmtree(cls.data_loc)
                cls.create_test_data_points(
                    all_projects,
                    cls.files_per_project,
                    cls.data_loc,
                    cls.sentence_db_loc,
                )

        cls.sentence_db = SentenceDB.load(cls.sentence_db_loc)
        all_files = cls.load_files(cls.data_loc, cls.sentence_db)

        cls.test_files: list[DatasetFile] = []
        cls.val_files: list[DatasetFile] = []
        cls.train_files: list[DatasetFile] = []

        for file in all_files:
            if Path(file.file_context.repository).name in cls.test_projects:
                cls.test_files.append(file)
            elif Path(file.file_context.repository).name in cls.val_projects:
                cls.val_files.append(file)
            else:
                cls.train_files.append(file)

        assert len(cls.test_files) == len(cls.test_projects) * cls.files_per_project
        assert len(cls.val_files) == len(cls.val_projects) * cls.files_per_project
        assert len(cls.train_files) == len(all_projects) * cls.files_per_project

    @classmethod
    def teardown_class(cls):
        cls.sentence_db.close()


if __name__ == "__main__":
    TestSplits.setup_class()
    try:
        TestSplits().test_create_predefined_data_split()
    finally:
        TestSplits.teardown_class()
