from __future__ import annotations
from typing import Any, Generator
from dataclasses import dataclass

import os
import sys
import argparse
import random
import json

from typeguard import typechecked
import yaml
from tqdm import tqdm

from data_management.splits import FileInfo, DataSplit, Split, split2str, str2split

@typechecked
class StepIndex:
    def __init__(self, proof_idx: int, step_idx: int) -> None:
        self.proof_idx = proof_idx
        self.step_idx = step_idx

    def to_json(self) -> Any:
        return {
            "proof_idx": self.proof_idx,
            "step_idx": self.step_idx,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> StepIndex:
        proof_idx = json_data["proof_idx"]
        step_idx = json_data["step_idx"]
        return cls(proof_idx, step_idx)


class AllSteps:
    pass

@dataclass
class CertainSteps:
    steps: list[StepIndex]

SelectedSteps = AllSteps | CertainSteps


@typechecked
class CompleteSample:
    ALIAS = "CompleteSample"

    def __init__(self, data_split: DataSplit, split: Split, data_loc: str) -> None:
        self.data_split = data_split
        self.split = split
        self.data_loc = data_loc

    def to_json(self) -> Any:
        return {
            "data_split": self.data_split.to_json(),
            "split": split2str(self.split),
            "data_loc": self.data_loc,
        }

    def step_generator(
        self,
    ) -> Generator[tuple[FileInfo, SelectedSteps], None, None]:
        for file in self.data_split.get_file_list(self.data_loc, self.split):
            yield (file, AllSteps())

    @classmethod
    def from_json(cls, json_data: Any) -> CompleteSample:
        data_split = DataSplit.from_json(json_data["data_split"])
        split = str2split(json_data["split"])
        data_loc = json_data["data_loc"]
        return cls(data_split, split, data_loc)

    @classmethod
    def __create(
        cls, data_split: DataSplit, split: Split, data_loc: str
    ) -> CompleteSample:
        return cls(data_split, split, data_loc)

    @classmethod
    def create(cls, conf: Any) -> CompleteSample:
        data_split = DataSplit.load(conf["data_split_loc"])
        split = str2split(conf["split"])
        data_loc = conf["data_loc"]
        return cls.__create(data_split, split, data_loc)


@typechecked
class RandomSample:
    ALIAS = "RandomSample"

    def __init__(
        self,
        steps_by_file: list[tuple[FileInfo, list[StepIndex]]],
        data_split: DataSplit,
        split: Split,
        data_loc: str,
        seed: int,
        prop: float,
    ) -> None:
        self.steps_by_file = steps_by_file
        self.data_split = data_split
        self.split = split
        self.data_loc = data_loc
        self.seed = seed
        self.prop = prop

    def __steps_by_file_to_json(self) -> Any:
        json_steps: list[Any] = []
        for f, steps in self.steps_by_file:
            f_data = {"0": f.to_json(), "1": [s.to_json() for s in steps]}
            json_steps.append(f_data)
        return json_steps

    @staticmethod
    def __steps_by_file_from_json(
        steps_by_file_data: Any,
    ) -> list[tuple[FileInfo, list[StepIndex]]]:
        steps_by_file: list[tuple[FileInfo, list[StepIndex]]] = []
        for f_data in steps_by_file_data:
            file = FileInfo.from_json(f_data["0"])
            steps = [StepIndex.from_json(s) for s in f_data["1"]]
            steps_by_file.append((file, steps))
        return steps_by_file

    def to_json(self) -> Any:
        return {
            "steps_by_file": self.__steps_by_file_to_json(),
            "data_split": self.data_split.to_json(),
            "split": split2str(self.split),
            "data_loc": self.data_loc,
            "seed": self.seed,
            "prop": self.prop,
        }

    def step_generator(
        self,
    ) -> Generator[tuple[FileInfo, SelectedSteps], None, None]:
        for file, step_idxs in self.steps_by_file:
            yield (file, CertainSteps(step_idxs))

    @classmethod
    def from_json(cls, json_data: Any) -> RandomSample:
        steps_by_file = cls.__steps_by_file_from_json(json_data["steps_by_file"])
        data_split = DataSplit.from_json(json_data["data_split"])
        split = str2split(json_data["split"])
        data_loc = json_data["data_loc"]
        seed = json_data["seed"]
        prop = json_data["prop"]
        return cls(steps_by_file, data_split, split, data_loc, seed, prop)

    @classmethod
    def __create(
        cls,
        data_split: DataSplit,
        split: Split,
        data_loc: str,
        sample_prop: float,
        seed: int,
    ) -> RandomSample:
        assert 0 <= sample_prop <= 1
        random.seed(seed)
        steps_by_file: list[tuple[FileInfo, list[StepIndex]]] = []
        for project in tqdm(data_split.get_project_list(split)):
            for file in project.files:
                proofs = file.get_proofs(data_loc)
                file_steps: list[StepIndex] = []
                for proof_idx, proof in enumerate(proofs):
                    for step_idx, _ in enumerate(proof.steps):
                        if random.random() <= sample_prop:
                            file_steps.append(StepIndex(proof_idx, step_idx))
                steps_by_file.append((file, file_steps))
        abs_data_loc = os.path.abspath(data_loc)
        return cls(steps_by_file, data_split, split, abs_data_loc, seed, sample_prop)

    @classmethod
    def create(cls, conf: Any) -> RandomSample:
        data_split = DataSplit.load(conf["data_split_loc"])
        split = str2split(conf["split"])
        data_loc = conf["data_loc"]
        sample_prop = conf["sample_prop"]
        seed = conf["seed"]
        return cls.__create(data_split, split, data_loc, sample_prop, seed)


class TacticClusteredSample:
    pass


class ProjectClusteredSample:
    pass


class ProjectClusteredThmTiedSample:
    pass


ExampleSample = CompleteSample | RandomSample


class SampleTypeNotFoundError(Exception):
    pass


def save_sample(sample: ExampleSample, save_path: str) -> None:
    save_dirname = os.path.dirname(save_path)
    if os.path.exists(save_path):
        raise FileExistsError(f"{save_path} exists.")
    if not os.path.exists(save_dirname):
        os.makedirs(save_dirname)
    with open(save_path, "w") as fout:
        json_obj = sample_to_json(sample)
        fout.write(json.dumps(json_obj, indent=2))


def load_sample(load_path: str) -> ExampleSample:
    with open(load_path, "r") as fin:
        json_data = json.load(fin)
    return sample_from_json(json_data)


def sample_to_json(sample: ExampleSample) -> Any:
    match sample:
        case CompleteSample():
            return {"alias": CompleteSample.ALIAS} | sample.to_json()
        case RandomSample():
            return {"alias": RandomSample.ALIAS} | sample.to_json()


def sample_from_json(json_data: Any) -> ExampleSample:
    attempted_alias = json_data["alias"]
    match attempted_alias:
        case CompleteSample.ALIAS:
            return CompleteSample.from_json(json_data)
        case RandomSample.ALIAS:
            return RandomSample.from_json(json_data)
        case _:
            raise SampleTypeNotFoundError(f"Unknown sample alias: {attempted_alias}")


def create(conf: Any) -> ExampleSample:
    match conf["alias"]:
        case "CompleteSample":
            return CompleteSample.create(conf)
        case "RandomSample":
            return RandomSample.create(conf)
        case _:
            alias_attempt = conf["alias"]
            raise SampleTypeNotFoundError(f"Unknown Sample type: {alias_attempt}")


def __load_config(config_loc: str) -> Any:
    with open(config_loc, "r") as fin:
        return yaml.load(fin, Loader=yaml.Loader)


if __name__ == "__main__":
    parser = argparse.ArgumentParser("Create a sampler over the dataset.")
    parser.add_argument(
        "sampler_config", help="Path to the config file for the sampler."
    )
    parser.add_argument("save_loc", help="Where to save the sampler.")
    args = parser.parse_args(sys.argv[1:])
    conf = __load_config(args.sampler_config)
    save_sample(create(conf), args.save_loc)
