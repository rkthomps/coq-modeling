"""
Given a folder with a bunch of repositories, 
create a project-wise split according to time. 
"""
from __future__ import annotations

import typeguard
import argparse


@typeguard.typechecked
class DataSplit:
    def __init__(
        self,
        train_projects: list[str],
        val_projects: list[str],
        test_projects: list[str],
        time_sorted: bool,
    ) -> None:
        self.train_projects = train_projects
        self.val_projects = val_projects
        self.test_projects = test_projects
        self.time_sorted = time_sorted

    @classmethod
    def __create_time_sorted(cls, data_loc: str) -> DataSplit:
        pass

    @classmethod
    def __create_random(cls, data_loc: str) -> DataSplit:
        pass

    @classmethod
    def create(cls, data_loc: str, time_sorted: bool) -> DataSplit:
        pass


if __name__ == "__main__":
    parser = argparse.ArgumentParser("Create a train/val/test split.")
