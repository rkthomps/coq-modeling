"""
Given a folder with a bunch of repositories, 
create a project-wise split according to time. 
"""

from __future__ import annotations
from typing import Optional
import sys, os
import re
from typing import Any
import datetime
import random
import math
import json
import requests
from enum import Enum
from dataclasses import dataclass
import functools
import yaml
from pathlib import Path

import ipdb
import argparse

import git
from tqdm import tqdm

from data_management.create_file_data_point import DATASET_PREFIX
from data_management.dataset_file import (
    DatasetFile,
    FileContext,
    Proof,
)
from data_management.sentence_db import SentenceDB

from coqpyt.coq.structs import TermType
from util.util import get_basic_logger
from util.constants import DATA_POINTS_NAME, REPOS_NAME

_logger = get_basic_logger(__name__)


RANDOM_SEED = 0


def get_all_files(data_splits: list[DataSplit]) -> list[FileInfo]:
    f_infos: list[FileInfo] = []
    seen_file_infos: set[FileInfo] = set()
    for ds in data_splits:
        for split in Split:
            for f_info in ds.get_file_list(split):
                if f_info not in seen_file_infos:
                    f_infos.append(f_info)
                    seen_file_infos.add(f_info)
    return f_infos


def get_dp_name(file: Path, data_loc: Path) -> str:
    return str(file.relative_to(data_loc / REPOS_NAME)).replace("/", "-")


def info_from_path(file: Path, workspace: Path, data_loc: Path) -> FileInfo:
    return FileInfo(
        get_dp_name(file, data_loc),
        str(file.relative_to(data_loc)),
        str(workspace.relative_to(data_loc)),
        workspace.name,
    )


class FileInfo:
    def __init__(
        self,
        dp_name: str,
        file: str,
        workspace: str,
        repository: str,
    ) -> None:
        self.dp_name = dp_name
        self.file = file
        self.workspace = workspace
        self.repository = repository

    def __hash__(self) -> int:
        return hash((self.dp_name, self.file, self.workspace, self.repository))

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, FileInfo):
            return False
        return (
            self.dp_name == other.dp_name
            and self.file == other.file
            and self.workspace == other.workspace
            and self.repository == other.repository
        )

    def get_dp(self, data_loc: Path, sentence_db: SentenceDB) -> DatasetFile:
        dp_loc = data_loc / DATA_POINTS_NAME / self.dp_name
        tmp_dp_loc = Path("/tmp") / DATA_POINTS_NAME / self.dp_name
        if tmp_dp_loc.exists():
            return DatasetFile.load(tmp_dp_loc, sentence_db)
        return DatasetFile.load(dp_loc, sentence_db)

    def get_proofs(self, data_loc: Path, sentence_db: SentenceDB) -> list[Proof]:
        dp_loc = data_loc / DATA_POINTS_NAME / self.dp_name
        tmp_dp_loc = Path("/tmp") / DATA_POINTS_NAME / self.dp_name
        if tmp_dp_loc.exists():
            dset_file = DatasetFile.load(tmp_dp_loc, sentence_db, metadata_only=True)
        else:
            dset_file = DatasetFile.load(dp_loc, sentence_db, metadata_only=True)
        return dset_file.proofs

    @functools.cache
    def get_theorems(self, data_loc: Path, sentence_db: SentenceDB) -> set[str]:
        thms: set[str] = set()
        for proof in self.get_proofs(data_loc, sentence_db):
            if proof.theorem.term.sentence_type == TermType.DEFINITION:
                # We don't care about examples
                continue
            thms.add(proof.theorem.term.text)
        return thms

    def __repr__(self) -> str:
        return str(self.__dict__)

    def to_json(self) -> Any:
        return {
            "dp_name": self.dp_name,
            "file": self.file,
            "workspace": self.workspace,
            "repository": self.repository,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> FileInfo:
        dp_name = json_data["dp_name"]
        file = json_data["file"]
        workspace = json_data["workspace"]
        repository = json_data["repository"]
        return cls(dp_name, file, workspace, repository)

    @classmethod
    def incomplete_from_file(cls, file: str) -> FileInfo:
        dp_name = file
        workspace = ""
        repository = ""
        return cls(dp_name, file, workspace, repository)


class Split(Enum):
    TRAIN = 0
    VAL = 1
    TEST = 2


def str2split(s: str) -> Split:
    match s:
        case "train":
            return Split.TRAIN
        case "val":
            return Split.VAL
        case "test":
            return Split.TEST
        case _:
            raise ValueError(f"Invalid Split {s}.")


def split2str(sp: Split) -> str:
    match sp:
        case Split.TRAIN:
            return "train"
        case Split.VAL:
            return "val"
        case Split.TEST:
            return "test"


def file_from_split(file: str, data_split: DataSplit) -> tuple[FileInfo, Split]:
    for split in Split:
        for file_info in data_split.get_file_list(split):
            if file == file_info.file:
                return file_info, split
    raise ValueError(f"Could not find file {file} in split.")


@dataclass
class DataSplit:
    train_files: list[FileInfo]
    val_files: list[FileInfo]
    test_files: list[FileInfo]

    def get_file_list(self, split: Split) -> list[FileInfo]:
        random.seed(RANDOM_SEED)
        match split:
            case Split.TRAIN:
                train_copy = self.train_files.copy()
                random.shuffle(train_copy)
                return train_copy
            case Split.VAL:
                val_copy = self.val_files.copy()
                random.shuffle(val_copy)
                return val_copy
            case Split.TEST:
                test_copy = self.test_files.copy()
                random.shuffle(test_copy)
                return test_copy

    def to_json(self) -> Any:
        return {
            "train_files": [tf.to_json() for tf in self.train_files],
            "val_files": [vf.to_json() for vf in self.val_files],
            "test_files": [tf.to_json() for tf in self.test_files],
        }

    def save(self, save_loc: Path) -> None:
        save_dir = os.path.dirname(save_loc)
        if not os.path.exists(save_dir) and 0 < len(save_dir):
            os.makedirs(save_dir)
        with open(save_loc, "w") as fout:
            fout.write(json.dumps(self.to_json(), indent=2))

    @classmethod
    def from_json(cls, json_data: Any) -> DataSplit:
        train_files = [FileInfo.from_json(tf) for tf in json_data["train_files"]]
        val_files = [FileInfo.from_json(vf) for vf in json_data["val_files"]]
        test_files = [FileInfo.from_json(tf) for tf in json_data["test_files"]]
        return cls(train_files, val_files, test_files)

    @classmethod
    def load(cls, path: Path) -> DataSplit:
        with path.open("r") as fin:
            json_data = json.load(fin)
        return cls.from_json(json_data)

    @classmethod
    def index_files(
        cls, data_loc: Path, sentence_db: SentenceDB
    ) -> list[tuple[FileInfo, set[str]]]:
        files: list[tuple[FileInfo, set[str]]] = []
        for f in (data_loc / DATA_POINTS_NAME).iterdir():
            f_dp = DatasetFile.load(f, sentence_db, metadata_only=True)
            assert f_dp.file_context.file.startswith(str(DATASET_PREFIX))
            assert f_dp.file_context.workspace.startswith(str(DATASET_PREFIX))
            assert f_dp.file_context.repository.startswith(str(DATASET_PREFIX))
            dp_thms: set[str] = set()
            for proof in f_dp.proofs:
                dp_thms.add(proof.theorem.term.text)
            f_info_file = str(
                Path(f_dp.file_context.file).resolve().relative_to(DATASET_PREFIX)
            )
            f_info_workspace = str(
                Path(f_dp.file_context.workspace).resolve().relative_to(DATASET_PREFIX)
            )
            f_info = FileInfo(
                f_dp.dp_name,
                f_info_file,
                f_info_workspace,
                f_info_workspace,
            )
            files.append((f_info, dp_thms))
        return files

    @classmethod
    def void_split(cls) -> DataSplit:
        return cls([], [], [])

    @classmethod
    def create(
        cls, split_config: SplitConfig, data_loc: Path, sentence_db: SentenceDB
    ) -> DataSplit:
        match split_config:
            case RandomSplitConfig():
                return cls.create_random_file_split(
                    data_loc,
                    sentence_db,
                    split_config.train_prop,
                    split_config.val_prop,
                    split_config.test_prop,
                )
            case PredefinedSplitConfig():
                return cls.create_predefined(
                    data_loc,
                    sentence_db,
                    split_config.test_projects,
                    split_config.val_projects,
                )

    @classmethod
    def create_random_file_split(
        cls,
        data_loc: Path,
        sentence_db: SentenceDB,
        train_pct: float,
        val_pct: float,
        test_pct: float,
    ) -> DataSplit:
        all_files = cls.index_files(data_loc, sentence_db)
        num_train = math.floor(train_pct * len(all_files))
        num_val = math.floor(val_pct * len(all_files))

        random.seed(RANDOM_SEED)
        random.shuffle(all_files)

        train_files = [f for f, _ in all_files[:num_train]]
        val_files = [f for f, _ in all_files[num_train : num_train + num_val]]
        test_files = [f for f, _ in all_files[num_train + num_val :]]
        return cls(train_files, val_files, test_files)

    @classmethod
    def create_predefined(
        cls,
        data_loc: Path,
        sentence_db: SentenceDB,
        test_projects: list[Path],
        val_projects: list[Path],
    ) -> DataSplit:
        all_files = cls.index_files(data_loc, sentence_db)

        test_files: list[FileInfo] = []
        test_thms: set[str] = set()
        resolved_test_projects = set(p.resolve() for p in test_projects)
        for f, thms in all_files:
            if (
                data_loc / REPOS_NAME / f.repository
            ).resolve() in resolved_test_projects:
                test_files.append(f)
                test_thms |= thms

        val_files: list[FileInfo] = []
        val_thms: set[str] = set()
        resolved_val_projects = set(p.resolve() for p in val_projects)
        for f, thms in all_files:
            if not thms.isdisjoint(test_thms):
                continue
            if (
                data_loc / REPOS_NAME / f.repository
            ).resolve() in resolved_val_projects:
                val_files.append(f)
                val_thms |= thms

        train_files: list[FileInfo] = []
        train_thms: set[str] = set()
        val_test_thms = val_thms | test_thms
        for f, thms in all_files:
            if not thms.isdisjoint(val_test_thms):
                continue
            repo_loc = data_loc / REPOS_NAME / f.repository
            if (
                repo_loc.resolve() in resolved_test_projects
                or repo_loc.resolve() in resolved_val_projects
            ):
                continue
            train_files.append(f)
            train_thms |= thms
        return cls(train_files, val_files, test_files)


@dataclass
class RandomSplitConfig:
    train_prop: float
    val_prop: float
    test_prop: float
    ALIAS = "random"

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> RandomSplitConfig:
        train_prop = yaml_data["train"]
        val_prop = yaml_data["val"]
        test_prop = yaml_data["test"]
        assert train_prop + val_prop + test_prop == 1
        return cls(train_prop, val_prop, test_prop)


@dataclass
class PredefinedSplitConfig:
    test_projects: list[Path]
    val_projects: list[Path]
    ALIAS = "predefined"

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> PredefinedSplitConfig:
        test_projects = [Path(p) for p in yaml_data["test_projects"]]
        val_projects = [Path(p) for p in yaml_data["val_projects"]]
        assert all([p.exists() for p in test_projects])
        assert all([p.exists() for p in val_projects])
        return cls(test_projects, val_projects)


SplitConfig = RandomSplitConfig | PredefinedSplitConfig


def split_config_from_yaml(yaml_data: Any) -> SplitConfig:
    match yaml_data["attempted_alias"]:
        case RandomSplitConfig.ALIAS:
            return RandomSplitConfig.from_yaml(yaml_data)
        case PredefinedSplitConfig.ALIAS:
            return PredefinedSplitConfig.from_yaml(yaml_data)
        case _:
            raise ValueError(
                f"Invalid split config alias {yaml_data['attempted_alias']}."
            )


if __name__ == "__main__":
    parser = argparse.ArgumentParser("Create a train/val/test split.")
    parser.add_argument(
        "--data_loc", required=True, help="Directory above 'repos' and 'data_points'."
    )
    parser.add_argument(
        "--sentence_db_loc", required=True, help="Path to sentence database."
    )
    parser.add_argument(
        "--split_config",
        required=True,
        help="yaml file containing the split configuration.",
    )
    parser.add_argument("--save_loc", required=True, help="Location to save the split.")

    args = parser.parse_args()
    data_loc = Path(args.data_loc)
    sentence_db_loc = Path(args.sentence_db_loc)
    split_config_loc = Path(args.split_config)
    save_loc = Path(args.save_loc)

    assert data_loc.exists()
    assert sentence_db_loc.exists()
    assert split_config_loc.exists()
    if save_loc.exists():
        raise FileExistsError(f"{save_loc} exists.")

    with split_config_loc.open("r") as fin:
        split_config_yaml = yaml.safe_load(fin)

    split_config = split_config_from_yaml(split_config_yaml)
    sentence_db = SentenceDB.load(sentence_db_loc)
    split = DataSplit.create(split_config, data_loc, sentence_db)
    split.save(save_loc)
