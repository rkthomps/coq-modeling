from __future__ import annotations
from typing import Any
from tqdm import tqdm
import ipdb
import shutil

import sys, os
import argparse
import yaml
import json
import math

from dataclasses import dataclass
from data_management.splits import DataSplit, Split, FileInfo, str2split
from model_deployment.model_wrapper import ModelWrapper, wrapper_from_conf

from util.util import get_basic_logger

_logger = get_basic_logger(__name__)

ATTEMPTS_NAME = "files"


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

    def margin(self) -> float:
        return 1.96 * math.sqrt(
            self.compute() * (1 - self.compute()) / self.attempted_steps
        )

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
class StepAttempt:
    input: str
    predictions: list[str]
    ground_truth: list[str]
    all_proof_steps: list[str]

    def has_k(self, k: int) -> bool:
        return 0 <= k < len(self.predictions)

    def is_correct_at_k(self, k: int) -> bool:
        prediction_k = self.predictions[k]
        split_prediction = prediction_k.split()
        split_ground_truth = "".join(self.ground_truth).split()
        return split_ground_truth[: (len(split_prediction))] == split_prediction

    def to_json(self) -> Any:
        return {
            "input": self.input,
            "predictions": self.predictions,
            "ground_truth": self.ground_truth,
            "all_proof_steps": self.all_proof_steps,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> StepAttempt:
        input = json_data["input"]
        predictions = json_data["predictions"]
        ground_truth = json_data["ground_truth"]
        ground_truth_context = json_data["all_proof_steps"]
        return cls(input, predictions, ground_truth, ground_truth_context)


@dataclass
class FileEval:
    file_info: FileInfo
    step_attempts: list[StepAttempt]

    def to_json(self) -> Any:
        return {
            "file_info": self.file_info.to_json(),
            "step_attempts": [a.to_json() for a in self.step_attempts],
        }

    def save(self, path: str) -> None:
        path_dirname = os.path.dirname(path)
        os.makedirs(path_dirname, exist_ok=True)
        with open(path, "w") as fout:
            fout.write(json.dumps(self.to_json(), indent=2))

    @classmethod
    def load(cls, path: str) -> FileEval:
        with open(path, "r") as fin:
            json_data = json.load(fin)
            return cls.from_json(json_data)

    @classmethod
    def from_json(cls, json_data: Any) -> FileEval:
        file_info = FileInfo.from_json(json_data["file_info"])
        step_attempts = [StepAttempt.from_json(s) for s in json_data["step_attempts"]]
        return cls(file_info, step_attempts)


def evaluate(conf: StringEvalConf) -> None:
    file_list = conf.data_split.get_file_list(conf.split)
    for file_info in tqdm(file_list):
        try:
            dp_obj = file_info.get_dp(conf.data_loc)
            attempts: list[StepAttempt] = []
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
                    next_ground_truth = ground_truth_steps[i:]
                    attempt = StepAttempt(
                        example.input,
                        model_result.next_tactic_list[: conf.n_recs],
                        next_ground_truth,
                        ground_truth_steps,
                    )
                    attempts.append(attempt)
            if 0 < len(attempts):
                file_eval = FileEval(file_info, attempts)
                file_eval.save(
                    os.path.join(conf.save_loc, ATTEMPTS_NAME, file_info.dp_name)
                )
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
