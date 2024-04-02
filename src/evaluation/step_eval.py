from __future__ import annotations
from typing import Any, Optional
from tqdm import tqdm
import ipdb
import shutil

import sys, os
import argparse
import yaml
import json
import math

from dataclasses import dataclass
from data_management.dataset_file import Sentence, DatasetFile, Proof
from data_management.splits import DataSplit, Split, FileInfo, str2split
from model_deployment.model_wrapper import ModelWrapper, wrapper_from_conf
from util.util import LOGGER


ATTEMPTS_NAME = "files"


@dataclass
class StepEvalConf:
    split: Split
    data_split: DataSplit
    data_loc: str
    model_wrapper: ModelWrapper
    n_recs: int
    save_loc: str

    @classmethod
    def from_conf(cls, conf: Any) -> StepEvalConf:
        split = str2split(conf["split"])
        data_split = DataSplit.load(conf["data_split_loc"])
        data_loc = conf["data_loc"]
        model_wrapper = wrapper_from_conf(conf["model_wrapper"])
        n_recs = conf["n_recs"]
        save_loc = conf["save_loc"]
        return cls(split, data_split, data_loc, model_wrapper, n_recs, save_loc)


@dataclass
class NoPremiseStepAttempt:
    input: str
    predictions: list[str]
    ground_truth: list[str]
    all_proof_steps: list[str]

    def has_k(self, k: int) -> bool:
        return 0 <= k < len(self.predictions)

    def is_correct_at_k(self, k: int) -> bool:
        if k < 0:
            return False
        if len(self.predictions) <= k:
            return self.is_correct_at_k(k - 1)
        prediction_k = self.predictions[k]
        split_prediction = prediction_k.split()
        split_ground_truth = "".join(self.ground_truth).split()
        return (
            split_ground_truth[: (len(split_prediction))] == split_prediction
        ) or self.is_correct_at_k(k - 1)

    def to_json(self) -> Any:
        return {
            "input": self.input,
            "predictions": self.predictions,
            "ground_truth": self.ground_truth,
            "all_proof_steps": self.all_proof_steps,
        }

    def to_annotated_step_attempt(self, dp_obj: DatasetFile) -> StepAttempt:
        the_proof: Optional[Proof] = None
        for proof in dp_obj.proofs:
            ground_truth_steps = [s.step.text for s in proof.steps]
            if ground_truth_steps == self.all_proof_steps:
                the_proof = proof
        if the_proof is None:
            raise ValueError(f"Could not find proof in file {dp_obj.file_context.file}")
        new_annotated_steps = [
            AnnotatedStep(s.step.text, s.step.context) for s in the_proof.steps
        ]
        new_ground_truth = new_annotated_steps[
            (len(new_annotated_steps) - len(self.ground_truth)) :
        ]
        return StepAttempt(
            self.input, self.predictions, new_ground_truth, new_annotated_steps
        )

    @classmethod
    def from_json(cls, json_data: Any) -> NoPremiseStepAttempt:
        input = json_data["input"]
        predictions = json_data["predictions"]
        ground_truth = json_data["ground_truth"]
        ground_truth_context = json_data["all_proof_steps"]
        return cls(input, predictions, ground_truth, ground_truth_context)


@dataclass
class AnnotatedStep:
    step_text: str
    step_context: list[Sentence]

    def to_json(self) -> Any:
        return {
            "step_text": self.step_text,
            "step_context": [c.to_json() for c in self.step_context],
        }

    @classmethod
    def from_json(cls, json_data: Any) -> AnnotatedStep:
        step_text = json_data["step_text"]
        context = [Sentence.from_json(s) for s in json_data["step_context"]]
        return cls(step_text, context)


@dataclass
class StepAttempt:
    input: str
    predictions: list[str]
    ground_truth: list[AnnotatedStep]
    all_proof_steps: list[AnnotatedStep]

    def has_k(self, k: int) -> bool:
        return 0 <= k < len(self.predictions)

    def requires_premise(self) -> bool:
        return 0 < len(self.ground_truth[0].step_context)

    def is_correct_at_k(self, k: int) -> bool:
        if k < 0:
            return False
        if len(self.predictions) <= k:
            return self.is_correct_at_k(k - 1)
        prediction_k = self.predictions[k]
        split_prediction = prediction_k.split()
        ground_truth_texts = [g.step_text for g in self.ground_truth]
        split_ground_truth = "".join(ground_truth_texts).split()
        return (
            split_ground_truth[: (len(split_prediction))] == split_prediction
        ) or self.is_correct_at_k(k - 1)

    def to_json(self) -> Any:
        return {
            "input": self.input,
            "predictions": self.predictions,
            "ground_truth": [g.to_json() for g in self.ground_truth],
            "all_proof_steps": [s.to_json() for s in self.all_proof_steps],
        }

    @classmethod
    def from_json(cls, json_data: Any) -> StepAttempt:
        input = json_data["input"]
        predictions = json_data["predictions"]
        ground_truth = [AnnotatedStep.from_json(g) for g in json_data["ground_truth"]]
        all_proof_steps = [
            AnnotatedStep.from_json(s) for s in json_data["all_proof_steps"]
        ]
        return cls(input, predictions, ground_truth, all_proof_steps)


@dataclass
class FileEvalOld:
    file_info: FileInfo
    step_attempts: list[NoPremiseStepAttempt]

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

    def correct_at(self, k: int) -> float:
        num_correct = 0
        for attempt in self.step_attempts:
            num_correct += attempt.is_correct_at_k(k)
        return num_correct / len(self.step_attempts)

    def correct_at_margin(self, k: int) -> float:
        correct_at = self.correct_at(k)
        return 1.96 * math.sqrt(correct_at * (1 - correct_at) / len(self.step_attempts))

    def to_file_eval_new(self, dp_obj: DatasetFile) -> FileEval:
        return FileEval(
            self.file_info,
            [s.to_annotated_step_attempt(dp_obj) for s in self.step_attempts],
        )

    @classmethod
    def load(cls, path: str) -> FileEvalOld:
        with open(path, "r") as fin:
            json_data = json.load(fin)
            return cls.from_json(json_data)

    @classmethod
    def from_json(cls, json_data: Any) -> FileEvalOld:
        file_info = FileInfo.from_json(json_data["file_info"])
        step_attempts = [
            NoPremiseStepAttempt.from_json(s) for s in json_data["step_attempts"]
        ]
        return cls(file_info, step_attempts)


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

    def correct_at(self, k: int) -> float:
        num_correct = 0
        for attempt in self.step_attempts:
            num_correct += attempt.is_correct_at_k(k)
        return num_correct / len(self.step_attempts)

    def correct_at_margin(self, k: int) -> float:
        correct_at = self.correct_at(k)
        return 1.96 * math.sqrt(correct_at * (1 - correct_at) / len(self.step_attempts))

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


def evaluate(conf: StepEvalConf) -> None:
    file_list = conf.data_split.get_file_list(conf.split)
    for file_info in tqdm(file_list):
        try:
            dp_obj = file_info.get_dp(conf.data_loc)
            attempts: list[StepAttempt] = []
            for proof in dp_obj.proofs:
                ground_truth_steps = [
                    AnnotatedStep(s.step.text, s.step.context) for s in proof.steps
                ]
                for i, step in enumerate(proof.steps):
                    example = conf.model_wrapper.formatter.example_from_step(
                        i,
                        proof,
                        dp_obj,
                        file_info,
                        conf.split,
                        conf.data_loc,
                        [s.step_text for s in ground_truth_steps],
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
            LOGGER.warning(f"Could not find file: {file_info.file}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Run a stepwise evaluation of a model")
    parser.add_argument(
        "eval_conf_loc", help="Location of configuration file for evaluation."
    )
    args = parser.parse_args(sys.argv[1:])
    with open(args.eval_conf_loc, "r") as fin:
        eval_config_data = yaml.load(fin, Loader=yaml.Loader)
    eval_conf = StepEvalConf.from_conf(eval_config_data)
    if os.path.exists(eval_conf.save_loc):
        raise FileExistsError(eval_conf.save_loc)
    os.makedirs(eval_conf.save_loc)
    shutil.copy(args.eval_conf_loc, eval_conf.save_loc)
    evaluate(eval_conf)
