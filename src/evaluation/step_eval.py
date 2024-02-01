from __future__ import annotations
from typing import Any
from tqdm import tqdm
import ipdb
import shutil

import sys, os
import argparse
import yaml
import json

from dataclasses import dataclass
from data_management.splits import DataSplit, Split, FileInfo, str2split
from model_deployment.model_wrapper import ModelWrapper, wrapper_from_conf

from util.util import get_basic_logger

_logger = get_basic_logger(__name__)


@dataclass
class StringEvalConf:
    split: Split
    data_split: DataSplit
    data_loc: str
    model_wrapper: ModelWrapper
    n_recs: int
    save_loc: str

    @classmethod
    def from_conf(cls, conf: Any) -> StringEvalConf:
        split = str2split(conf["split"])
        data_split = DataSplit.load(conf["data_split_loc"])
        data_loc = conf["data_loc"]
        model_wrapper = wrapper_from_conf(conf["model_wrapper"])
        n_recs = conf["n_recs"]
        save_loc = conf["save_loc"]
        return cls(split, data_split, data_loc, model_wrapper, n_recs, save_loc)


@dataclass
class StepStat:
    correct_steps: int
    attempted_steps: int

    def tick_correct(self) -> None:
        self.correct_steps += 1
        self.attempted_steps += 1

    def tick_incorrect(self) -> None:
        self.attempted_steps += 1

    def compute(self) -> float:
        return self.correct_steps / self.attempted_steps

    def to_json(self) -> Any:
        return {
            "correct_steps": self.correct_steps,
            "attempted_steps": self.attempted_steps,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> StepStat:
        return cls(json_data["correct_steps"], json_data["attempted_steps"])

    @classmethod
    def empty(cls) -> StepStat:
        return cls(0, 0)


@dataclass
class StepStats:
    stats_dict: dict[int, StepStat]
    file_info: FileInfo

    def tick_correct_at(self, k: int) -> None:
        if k not in self.stats_dict:
            self.stats_dict[k] = StepStat.empty()
        self.stats_dict[k].tick_correct()

    def tick_incorrect_at(self, k: int) -> None:
        if k not in self.stats_dict:
            self.stats_dict[k] = StepStat.empty()
        self.stats_dict[k].tick_incorrect()

    def at(self, k: int) -> StepStat:
        return self.stats_dict[k]

    def to_json(self) -> Any:
        return {
            "stats_dict": dict([(k, v.to_json()) for k, v in self.stats_dict.items()]),
            "file_info": self.file_info.to_json(),
        }

    def save(self, path: str) -> None:
        path_dir = os.path.dirname(path)
        os.makedirs(path_dir, exist_ok=True)
        with open(path, "w") as fout:
            fout.write(json.dumps(self.to_json()))

    @classmethod
    def empty(cls, file_info: FileInfo) -> StepStats:
        return cls({}, file_info)

    @classmethod
    def from_json(cls, json_data: Any) -> StepStats:
        stats_dict: dict[int, StepStat] = {}
        for k, v in json_data["stats_dict"].items():
            stats_dict[int(k)] = StepStat.from_json(v)
        file_info = FileInfo.from_json(json_data["file_info"])
        return cls(stats_dict, file_info)

    @classmethod
    def load(cls, path: str) -> StepStats:
        with open(path, "r") as fin:
            json_data = json.load(fin)
            return cls.from_json(json_data)


def evaluate(conf: StringEvalConf) -> None:
    file_list = conf.data_split.get_file_list(conf.split)
    num_files = 0
    for file_info in tqdm(file_list):
        file_stats = StepStats.empty(file_info)
        try:
            dp_obj = file_info.get_dp(conf.data_loc)
            for proof in dp_obj.proofs:
                ground_truth_steps = [s.step.text for s in proof.steps]
                for i, step in enumerate(proof.steps):
                    example = conf.model_wrapper.formatter.example_from_step(
                        i,
                        proof,
                        dp_obj,
                        file_info,
                        conf.split,
                        conf.data_loc,
                        ground_truth_steps,
                    )
                    model_result = conf.model_wrapper.get_recs(example, conf.n_recs)
                    next_ground_truth = "".join(ground_truth_steps[i:])
                    ground_truth_no_whitespace = next_ground_truth.split()
                    for i, tactic in enumerate(
                        model_result.next_tactic_list[: conf.n_recs]
                    ):
                        tac_no_whitespace = tactic.split()
                        tac_list_len = len(tac_no_whitespace)
                        if (
                            ground_truth_no_whitespace[:tac_list_len]
                            == tac_no_whitespace
                        ):
                            file_stats.tick_correct_at(i)
                        else:
                            file_stats.tick_incorrect_at(i)
                    _logger.info(
                        f"Proof rate {file_stats.at(0).compute()} after {file_stats.at(0).attempted_steps} steps."
                    )
            num_files += 1
            file_stats.save(os.path.join(conf.save_loc, "files", file_info.dp_name))
        except FileNotFoundError:
            _logger.warning(f"Could not find file: {file_info.file}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Run a stepwise evaluation of a model")
    parser.add_argument(
        "eval_conf_loc", help="Location of configuration file for evaluation."
    )
    args = parser.parse_args(sys.argv[1:])
    with open(args.eval_conf_loc, "r") as fin:
        eval_config_data = yaml.load(fin, Loader=yaml.Loader)
    eval_conf = StringEvalConf.from_conf(eval_config_data)
    if os.path.exists(eval_conf.save_loc):
        raise FileExistsError(eval_conf.save_loc)
    os.makedirs(eval_conf.save_loc)
    shutil.copy(args.eval_conf_loc, eval_conf.save_loc)
    evaluate(eval_conf)
