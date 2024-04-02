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
import time
import pytz
import requests
from enum import Enum
from dataclasses import dataclass
import functools
import yaml
import logging

import ipdb
import argparse

from typeguard import typechecked
import git
from tqdm import tqdm

from data_management.dataset_file import (
    DatasetFile,
    FileContext,
    FILE_CONTEXT_NAME,
    Proof,
)
from data_management.sentence_db import SentenceDB
from util.util import LOGGER

from coqpyt.coq.structs import TermType



REPOS_NAME = "repos"
DATA_POINTS_NAME = "data_points"

RANDOM_SEED = 0
INVALID_DATE = datetime.datetime(1900, 1, 1, tzinfo=pytz.timezone("US/Pacific"))


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

    def get_creation_time(self, workspace: str) -> datetime.datetime:
        try:
            repo_path = os.path.join(workspace, REPOS_NAME, self.repository)
            repo = git.Repo(repo_path)
            fst, *_ = repo.iter_commits(reverse=True)
            return fst.committed_datetime
        except:
            return INVALID_DATE

    def get_dp(self, data_loc: str, sentence_db: SentenceDB) -> DatasetFile:
        dp_loc = os.path.join(data_loc, DATA_POINTS_NAME, self.dp_name)
        return DatasetFile.load(dp_loc, sentence_db)

    def get_proofs(self, data_loc: str, sentence_db: SentenceDB) -> list[Proof]:
        dp_loc = os.path.join(data_loc, DATA_POINTS_NAME, self.dp_name)
        dset_file = DatasetFile.load(dp_loc, sentence_db, metadata_only=True)
        return dset_file.proofs

    @functools.cache
    def get_theorems(self, data_loc: str, sentence_db: SentenceDB) -> set[str]:
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


class ThmMap:
    def __init__(self, sentence_db: SentenceDB) -> None:
        self.thm_map: dict[str, tuple[FileInfo, set[str]]] = {}
        self.sentence_db = sentence_db

    def lookup(self, data_loc: str, dp_name: str) -> tuple[FileInfo, set[str]]:
        dp_loc = os.path.join(data_loc, DATA_POINTS_NAME, dp_name)
        if dp_loc in self.thm_map:
            return self.thm_map[dp_loc]
        dp_obj = DatasetFile.load(dp_loc, self.sentence_db, metadata_only=True)
        file_info = FileInfo(
            dp_name,
            dp_obj.file_context.file,
            dp_obj.file_context.workspace,
            dp_obj.file_context.repository,
        )

        thms: set[str] = set()
        for proof in dp_obj.proofs:
            if proof.theorem.term.sentence_type == TermType.DEFINITION:
                # We don't care about examples
                continue
            thms.add(proof.theorem.term.text)

        self.thm_map[dp_loc] = file_info, thms
        return file_info, thms

@typechecked
class Project:
    def __init__(self, repo_name: str, files: list[FileInfo]) -> None:
        self.repo_name = repo_name
        self.files = files

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Project):
            return False
        return self.repo_name == other.repo_name and self.files == other.files

    def to_json(self) -> Any:
        return {"repo_name": self.repo_name, "files": [f.to_json() for f in self.files]}

    def filter(self, forbidden_thms: set[str], data_loc: str) -> list[FileInfo]:
        good_files: list[FileInfo] = []
        for file in self.files:
            file_thms = file.get_theorems(data_loc)
            if len(file_thms.intersection(forbidden_thms)) == 0:
                good_files.append(file)
        return good_files

    def get_thms(self, data_loc: str, thm_map: ThmMap) -> set[str]:
        thms: set[str] = set()
        for file in self.files:
            _, file_thms = thm_map.lookup(data_loc, file.dp_name)
            thms |= file_thms
        return thms

    def get_creation_time(self, workspace: str) -> datetime.datetime:
        try:
            repo_path = os.path.join(workspace, REPOS_NAME, self.repo_name)
            repo = git.Repo(repo_path)
            fst, *_ = repo.iter_commits(reverse=True)
            return fst.committed_datetime
        except:
            return INVALID_DATE

    @classmethod
    def __count_star_items(cls, response: Any) -> int:
        match response:
            case [{"starred_at": _}, *l_rest]:
                return 1 + cls.__count_star_items(l_rest)
            case _:
                return 0

    @classmethod
    def __get_git_username_and_token(cls) -> tuple[str, str]:
        match os.environ:
            case {"GIT_USR": git_usr, "GIT_TOK": git_tok}:
                return git_usr, git_tok
            case _:
                raise ValueError(
                    "Must have GIT_USR and GIT_TOK env variables set to use git api to retreive repo stars."
                )

    def get_num_stars(self) -> int:
        split_start_idx = 0
        dash_idx = self.repo_name.find("-", split_start_idx)
        while 0 <= dash_idx < len(self.repo_name) - 1:
            usr = self.repo_name[:dash_idx]
            repo = self.repo_name[(dash_idx + 1) :]
            url = f"https://api.github.com/repos/{usr}/{repo}/stargazers"
            username, token = self.__get_git_username_and_token()
            repo_response = requests.get(
                url,
                headers={"Accept": "application/vnd.github.v3.star+json"},
                auth=(username, token),
            )
            try:
                return self.__count_star_items(repo_response.json())
            except ValueError:
                split_start_idx = dash_idx + 1
                dash_idx = self.repo_name.find("-", split_start_idx)
        return -1

    @classmethod
    def from_json(cls, json_data: Any) -> Project:
        repo_name = json_data["repo_name"]
        files = [FileInfo.from_json(f_data) for f_data in json_data["files"]]
        return cls(repo_name, files)


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


def split_file_path(
    parent_dir: str, split: Split, shuffled: bool = True, deduplicated: bool = True
) -> str:
    shuffled_str = "shuffled" if shuffled else "unshuffled"
    deduped_str = "deduplicated" if deduplicated else "undeduplicated"
    return os.path.join(
        parent_dir, f"{split2str(split)}-{deduped_str}-{shuffled_str}.jsonl"
    )


def file_from_split(file: str, data_split: DataSplit) -> tuple[FileInfo, Split]:
    for split in Split:
        for file_info in data_split.get_file_list(split):
            if file == file_info.file:
                return file_info, split
    raise ValueError(f"Could not find file {file} in split.")


@typechecked
class EvalProjects:
    def __init__(
        self, validation_projects: list[str], testing_projects: list[str]
    ) -> None:
        self.validation_projects = validation_projects
        self.testing_projects = testing_projects
        self._testing_name_set = set(self.get_testing_names())
        self._validation_name_set = set(self.get_validation_names())
        self.verify_format()

    def _verify_format(self, projects: list[str]) -> None:
        print("Verifying project formats")
        for p in tqdm(projects):
            if len(p.split("/")) != 2:
                raise ValueError(f"{p} does not match expected format user/proj")

    def verify_format(self) -> None:
        self._verify_format(self.testing_projects)
        self._verify_format(self.testing_projects)

    def get_projects(self, data_loc: str, project_names: list[str], thm_map: ThmMap) -> list[Project]:
        projects: list[Project] = []
        for project_name in project_names:
            LOGGER.info(f"Gathering project: {project_name}")
            project_files = DataSplit.find_files(data_loc, project_name, thm_map)
            if len(project_files) == 0:
                LOGGER.warning(f"Evaluation project {project_name} has no files.")
            projects.append(Project(project_name, project_files))
        return projects

    def name_available_for_training(self, candidate_name: str) -> bool:
        if candidate_name in self._testing_name_set:
            return False
        if candidate_name in self._validation_name_set:
            return False
        return True

    def get_testing_projects(self, data_loc: str, thm_map: ThmMap) -> list[Project]:
        return self.get_projects(data_loc, self.get_testing_names(), thm_map)

    def get_validation_projects(self, data_loc: str, thm_map: ThmMap) -> list[Project]:
        return self.get_projects(data_loc, self.get_validation_names(), thm_map)

    def get_testing_names(self) -> list[str]:
        return [tp.replace(os.path.sep, "-") for tp in self.testing_projects]

    def get_validation_names(self) -> list[str]:
        return [tp.replace(os.path.sep, "-") for tp in self.validation_projects]

    @classmethod
    def from_conf(cls, conf: Any) -> EvalProjects:
        val_projects = conf["val_projects"]
        test_projects = conf["test_projects"]
        return cls(val_projects, test_projects)


@typechecked
class DataSplit:
    def __init__(
        self,
        train_projects: list[Project],
        val_projects: list[Project],
        test_projects: list[Project],
    ) -> None:
        self.train_projects = train_projects
        self.val_projects = val_projects
        self.test_projects = test_projects

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, DataSplit):
            return False
        return (
            self.train_projects == other.train_projects
            and self.val_projects == other.val_projects
            and self.test_projects == other.test_projects
        )

    @staticmethod
    def __get_shuffled_files(projs: list[Project]) -> list[FileInfo]:
        flat_dps = [file for proj in projs for file in proj.files]
        random.seed(RANDOM_SEED)
        random.shuffle(flat_dps)
        return flat_dps

    def get_file_list(self, split: Split) -> list[FileInfo]:
        match split:
            case Split.TRAIN:
                return self.__get_shuffled_files(self.train_projects)
            case Split.VAL:
                return self.__get_shuffled_files(self.val_projects)
            case Split.TEST:
                return self.__get_shuffled_files(self.test_projects)

    def get_project_list(self, split: Split) -> list[Project]:
        match split:
            case Split.TRAIN:
                return self.train_projects
            case Split.VAL:
                return self.val_projects
            case Split.TEST:
                return self.test_projects

    def get_all_projects(self) -> list[Project]:
        return self.train_projects + self.val_projects + self.test_projects

    def to_json(self) -> Any:
        return {
            "train_projects": [tp.to_json() for tp in self.train_projects],
            "val_projects": [vp.to_json() for vp in self.val_projects],
            "test_projects": [tp.to_json() for tp in self.test_projects],
        }

    def save(self, save_loc: str) -> None:
        save_dir = os.path.dirname(save_loc)
        if not os.path.exists(save_dir) and 0 < len(save_dir):
            os.makedirs(save_dir)
        with open(save_loc, "w") as fout:
            fout.write(json.dumps(self.to_json(), indent=2))

    @classmethod
    def from_json(cls, json_data: Any) -> DataSplit:
        train_projects = [
            Project.from_json(tp_data) for tp_data in json_data["train_projects"]
        ]
        val_projects = [
            Project.from_json(vp_data) for vp_data in json_data["val_projects"]
        ]
        test_projects = [
            Project.from_json(tp_data) for tp_data in json_data["test_projects"]
        ]
        return cls(train_projects, val_projects, test_projects)

    @classmethod
    def load(cls, path: str) -> DataSplit:
        with open(path, "r") as fin:
            json_data = json.load(fin)
        return cls.from_json(json_data)

    @staticmethod
    def __strip_data_prefix(path: str, prefix: str) -> str:
        assert path.startswith(prefix)
        return os.path.relpath(path, prefix)

    @classmethod
    def find_files(cls, data_loc: str, repo_name: str, thm_map: ThmMap) -> list[FileInfo]:
        dp_loc = os.path.join(data_loc, DATA_POINTS_NAME)
        repo_qualified_name = os.path.join(REPOS_NAME, repo_name)
        files: list[FileInfo] = []
        for dp_name in os.listdir(dp_loc):
            if dp_name.startswith(repo_name):
                file_info, _ = thm_map.lookup(data_loc, dp_name)
                if not file_info.repository.endswith(repo_qualified_name):
                    continue
                prefix_len = len(file_info.repository) - len(repo_qualified_name)
                data_prefix = file_info.repository[:prefix_len]

                repo = cls.__strip_data_prefix(file_info.repository, data_prefix)
                file = cls.__strip_data_prefix(file_info.file, data_prefix)
                workspace = cls.__strip_data_prefix(file_info.workspace, data_prefix)

                file = FileInfo(dp_name, file, workspace, repo)
                files.append(file)
        return files

    @classmethod
    def __create_project_list(cls, data_loc: str, thm_map: ThmMap) -> list[Project]:
        repos_loc = os.path.join(data_loc, REPOS_NAME)
        projects: list[Project] = []

        print("Creating Project List...")
        for repo in tqdm(os.listdir(repos_loc)):
            LOGGER.info(f"Gathering project: {repo}")
            repo_files = cls.find_files(data_loc, repo, thm_map)
            if len(repo_files) == 0:
                continue
            projects.append(Project(repo, repo_files))
        return projects

    @classmethod
    def __get_ordered_project_list(
        cls, data_loc: str, time_sorted: bool, thm_map: ThmMap
    ) -> list[Project]:
        project_list = cls.__create_project_list(data_loc, thm_map)
        print("Sorting Project List...")
        if time_sorted:
            print("Getting Times...")
            project_times = [p.get_creation_time(data_loc) for p in tqdm(project_list)]
            sorted_projects = sorted(
                [(t, p) for t, p in zip(project_times, project_list)],
                key=lambda t: t[0],
            )
            return [v for _, v in sorted_projects]
        random.seed(RANDOM_SEED)
        random.shuffle(project_list)
        return project_list

    @classmethod
    def __assign_projects(
        cls, data_loc: str, project_list: list[Project], thm_map: ThmMap, train_cutoff: float = 0.8
    ) -> DataSplit:
        """
        Train gets first 80% of projects, and any projects with interecting
        theorems thereafter.
        """
        train_cutoff_num = math.ceil(train_cutoff * len(project_list))
        train_projs: list[Project] = project_list[:train_cutoff_num]
        train_thms: set[str] = set()
        print("Gathering training thms...")
        for train_proj in tqdm(train_projs):
            train_thms |= train_proj.get_thms(data_loc, thm_map)

        val_projs: list[Project] = []
        val_thms: set[str] = set()
        test_projs: list[Project] = []
        test_thms: set[str] = set()
        print("Assigning Projects...")
        for i, remaining_proj in tqdm(enumerate(project_list[train_cutoff_num:])):
            remaining_proj_thms = remaining_proj.get_thms(data_loc, thm_map)
            if len(remaining_proj_thms & train_thms) > 0:
                train_projs.append(remaining_proj)
                train_thms |= remaining_proj_thms
            elif len(remaining_proj_thms & val_thms) > 0:
                val_projs.append(remaining_proj)
                val_thms |= remaining_proj_thms
            elif i % 2 == 0:
                val_projs.append(remaining_proj)
                val_thms |= remaining_proj_thms
            else:
                test_projs.append(remaining_proj)
                test_thms |= remaining_proj_thms
        return cls(train_projs, val_projs, test_projs)

    @classmethod
    def void_split(cls) -> DataSplit:
        return cls([], [], [])

    @classmethod
    def create(cls, data_loc: str, sentence_db: SentenceDB, time_sorted: bool) -> DataSplit:
        thm_map = ThmMap(sentence_db)
        ordered_project_list = cls.__get_ordered_project_list(data_loc, time_sorted, thm_map)
        data_split = cls.__assign_projects(data_loc, ordered_project_list, thm_map)
        data_points_loc = os.path.join(data_loc, DATA_POINTS_NAME)
        num_raw_files = len(os.listdir(data_points_loc))
        print(f"Num raw files: {num_raw_files}")
        num_captured_files = (
            len(data_split.get_file_list(Split.TRAIN))
            + len(data_split.get_file_list(Split.VAL))
            + len(data_split.get_file_list(Split.TEST))
        )
        print(f"Num captured files: {num_captured_files}")
        return data_split

    @classmethod
    def create_from_list(cls, data_loc: str, sentence_db: SentenceDB, eval_projects: EvalProjects) -> DataSplit:
        thm_map = ThmMap(sentence_db)
        test_thms: set[str] = set()
        test_projects = eval_projects.get_testing_projects(data_loc, thm_map)

        print("Creating Test Split")
        for testing_project in tqdm(test_projects):
            test_thms |= testing_project.get_thms(data_loc, thm_map)

        print("Creating Val Split")
        val_thms: set[str] = set()
        val_projects: list[Project] = []
        raw_val_projects = eval_projects.get_validation_projects(data_loc, thm_map)
        for validation_project in tqdm(raw_val_projects):
            clean_files = validation_project.filter(test_thms, data_loc)
            clean_project = Project(validation_project.repo_name, clean_files)
            val_projects.append(clean_project)
            val_thms |= clean_project.get_thms(data_loc, thm_map)

        LOGGER.info("Creating Train Split")
        train_projects: list[Project] = []
        candidate_train_projects = cls.__create_project_list(data_loc, thm_map)
        for project in tqdm(candidate_train_projects):
            if eval_projects.name_available_for_training(project.repo_name):
                clean_files = project.filter(test_thms | val_thms, data_loc)
                clean_project = Project(project.repo_name, clean_files)
                train_projects.append(clean_project)

        final_test_thms = functools.reduce(
            set.union, [p.get_thms(data_loc, thm_map) for p in test_projects], set()
        )
        final_val_thms = functools.reduce(
            set.union, [p.get_thms(data_loc, thm_map) for p in val_projects], set()
        )
        final_train_thms = functools.reduce(
            set.union, [p.get_thms(data_loc, thm_map) for p in train_projects], set()
        )
        assert final_test_thms.isdisjoint(final_val_thms)
        assert final_val_thms.isdisjoint(final_train_thms)
        assert final_test_thms.isdisjoint(final_train_thms)

        final_split = cls(train_projects, val_projects, test_projects)
        print(f"Num training files: {len(final_split.get_file_list(Split.TRAIN))}")
        print(f"Num validation files: {len(final_split.get_file_list(Split.VAL))}")
        print(f"Num testing files: {len(final_split.get_file_list(Split.TEST))}")
        print()
        print(f"Num training theorems: {len(final_train_thms)}")
        print(f"Num validation theorems: {len(final_val_thms)}")
        print(f"Num testing theorems: {len(final_test_thms)}")
        return final_split


if __name__ == "__main__":
    parser = argparse.ArgumentParser("Create a train/val/test split.")
    parser.add_argument("data_loc", help="Directory above 'repos' and 'data_points'.")
    parser.add_argument("sentence_db", help="Path to sentence database.")
    parser.add_argument("save_loc", help="Location to save the split.")
    parser.add_argument(
        "eval_projects_config",
        help="yaml file containing which projects should be saved for validation and testing.",
    )

    # parser.add_argument(
    #     "--time_sorted",
    #     "-t",
    #     action="store_true",
    #     help="Sort the repos by creation date.",
    # )
    # data_split = DataSplit.create(args.data_loc, args.time_sorted)

    args = parser.parse_args(sys.argv[1:])
    if os.path.exists(args.save_loc):
        raise ValueError(f"{args.save_loc} exists.")

    sentence_db = SentenceDB.load(args.sentence_db)
    with open(args.eval_projects_config, "r") as fin:
        eval_config = yaml.load(fin, Loader=yaml.Loader)

    eval_projects = EvalProjects.from_conf(eval_config)
    data_split = DataSplit.create_from_list(args.data_loc, sentence_db, eval_projects)
    data_split.save(args.save_loc)
