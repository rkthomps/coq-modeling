"""
Given a folder with a bunch of repositories, 
create a project-wise split according to time. 
"""
from __future__ import annotations
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

import argparse

from typeguard import typechecked
import git
from tqdm import tqdm

from data_management.dataset_file import DatasetFile, FileContext, FILE_CONTEXT_NAME, Proof


REPOS_NAME = "repos"
DATA_POINTS_NAME = "data_points"

RANDOM_SEED = 0
INVALID_DATE = datetime.datetime(1900, 1, 1, tzinfo=pytz.timezone("US/Pacific"))


class FileInfo:
    def __init__(
        self, dp_name: str, file: str, workspace: str, repository: str
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
    
    def get_dp(self, data_loc: str) -> DatasetFile:
        dp_loc = os.path.join(data_loc, DATA_POINTS_NAME, self.dp_name)
        return DatasetFile.from_directory(dp_loc)
    
    def get_proofs(self, data_loc: str) -> list[Proof]:
        dp_loc = os.path.join(data_loc, DATA_POINTS_NAME, self.dp_name)
        return DatasetFile.get_proofs(dp_loc)

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

    def get_thms(self, workspace: str) -> set[str]:
        thms: set[str] = set()
        for file in self.files:
            dp_loc = os.path.join(workspace, DATA_POINTS_NAME, file.dp_name)
            proofs = DatasetFile.get_proofs(dp_loc)
            for proof in proofs:
                thms.add(proof.theorem.term.text)
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
    def __get_shuffled_files(projs: list[Project], data_loc: str) -> list[FileInfo]:
        flat_dps = [file for proj in projs for file in proj.files]
        random.seed(RANDOM_SEED)
        random.shuffle(flat_dps)
        return flat_dps

    def get_file_list(self, data_loc: str, split: Split) -> list[FileInfo]:
        match split:
            case Split.TRAIN:
                return self.__get_shuffled_files(self.train_projects, data_loc)
            case Split.VAL:
                return self.__get_shuffled_files(self.val_projects, data_loc)
            case Split.TEST:
                return self.__get_shuffled_files(self.test_projects, data_loc)

    def get_project_list(self, split: Split) -> list[Project]:
        match split:
            case Split.TRAIN:
                return self.train_projects
            case Split.VAL:
                return self.val_projects
            case Split.TEST:
                return self.test_projects

    def to_json(self) -> Any:
        return {
            "train_projects": [tp.to_json() for tp in self.train_projects],
            "val_projects": [vp.to_json() for vp in self.val_projects],
            "test_projects": [tp.to_json() for tp in self.test_projects],
        }

    def save(self, save_loc: str) -> None:
        save_dir = os.path.dirname(save_loc)
        if not os.path.exists(save_dir):
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
    def __get_psuedo_context(dp_loc: str) -> FileContext:
        fc_loc = os.path.join(dp_loc, FILE_CONTEXT_NAME)
        with open(fc_loc, "r") as fin:
            file_str = fin.read(1000)
            fc_match = re.match(
                r'\{"file": "(.*?)", "workspace": "(.*?)", "repository": "(.*?)"',
                file_str,
            )
            if fc_match:
                file, workspace, repository = fc_match.groups()
                return FileContext(file, workspace, repository, [])
            else:
                raise ValueError(
                    f"Fast pattern could not match string: {file_str[:80]}"
                )

    @classmethod
    def __find_files(cls, data_loc: str, repo_name: str) -> list[FileInfo]:
        dp_loc = os.path.join(data_loc, DATA_POINTS_NAME)
        repo_qualified_name = os.path.join(REPOS_NAME, repo_name)
        files: list[FileInfo] = []
        for dset_file in os.listdir(dp_loc):
            if dset_file.startswith(repo_name):
                dset_file_loc = os.path.join(dp_loc, dset_file)
                file_context = cls.__get_psuedo_context(dset_file_loc)
                if file_context.repository == repo_qualified_name:
                    file = FileInfo(
                        dset_file,
                        file_context.file,
                        file_context.workspace,
                        file_context.repository,
                    )
                    files.append(file)
        return files

    @classmethod
    def __create_project_list(cls, data_loc: str) -> list[Project]:
        repos_loc = os.path.join(data_loc, REPOS_NAME)
        projects: list[Project] = []

        print("Creating Project List...")
        for repo in tqdm(os.listdir(repos_loc)):
            repo_files = cls.__find_files(data_loc, repo)
            if len(repo_files) == 0:
                continue
            projects.append(Project(repo, repo_files))
        return projects

    @classmethod
    def __get_ordered_project_list(
        cls, data_loc: str, time_sorted: bool
    ) -> list[Project]:
        project_list = cls.__create_project_list(data_loc)
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
        cls, data_loc: str, project_list: list[Project], train_cutoff: float = 0.8
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
            train_thms |= train_proj.get_thms(data_loc)

        val_projs: list[Project] = []
        val_thms: set[str] = set()
        test_projs: list[Project] = []
        test_thms: set[str] = set()
        print("Assigning Projects...")
        for i, remaining_proj in tqdm(enumerate(project_list[train_cutoff_num:])):
            remaining_proj_thms = remaining_proj.get_thms(data_loc)
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
    def create(cls, data_loc: str, time_sorted: bool) -> DataSplit:
        ordered_project_list = cls.__get_ordered_project_list(data_loc, time_sorted)
        data_split = cls.__assign_projects(data_loc, ordered_project_list)
        data_points_loc = os.path.join(data_loc, DATA_POINTS_NAME)
        num_raw_files = len(os.listdir(data_points_loc))
        print(f"Num raw files: {num_raw_files}")
        num_captured_files = (
            len(data_split.get_file_list(data_loc, Split.TRAIN))
            + len(data_split.get_file_list(data_loc, Split.VAL))
            + len(data_split.get_file_list(data_loc, Split.TEST))
        )
        print(f"Num captured files: {num_captured_files}")
        return data_split


if __name__ == "__main__":
    parser = argparse.ArgumentParser("Create a train/val/test split.")
    parser.add_argument("data_loc", help="Directory above 'repos' and 'data_points'.")
    parser.add_argument("save_loc", help="Location to save the split.")
    parser.add_argument(
        "--time_sorted",
        "-t",
        action="store_true",
        help="Sort the repos by creation date.",
    )
    args = parser.parse_args(sys.argv[1:])
    if os.path.exists(args.save_loc):
        raise ValueError(f"{args.save_loc} exists.")
    data_split = DataSplit.create(args.data_loc, args.time_sorted)
    data_split.save(args.save_loc)
