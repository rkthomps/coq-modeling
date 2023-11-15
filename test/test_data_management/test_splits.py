import unittest
import os
import pdb

from data_management.splits import DataSplit, Project, FileInfo


class SplitsCase(unittest.TestCase):
    def test_partition_mini_dataset(self) -> None:
        ds = DataSplit.create(self.data_path, time_sorted=True)
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
        self.assertEqual(ds, expected_ds)

    def setUp(self) -> None:
        self.data_path = os.path.join("test", "test_files", "coq-mini-dataset")
        if not os.path.exists(self.data_path):
            raise FileNotFoundError(
                f"{self.data_path} not found. Run tests from root project dir."
            )
