from __future__ import annotations
from typing import Any, Optional
import sys, os
import argparse
import json
import multiprocessing
import math

from data_management.splits import FileInfo
from evaluation.step_eval import FileEval, StepAttempt, ATTEMPTS_NAME

SMALL_ATTEMPTS_NAME = "files-small"


class SmallAttempt:
    def __init__(
        self,
        input: str,
        predictions: list[str],
        ground_truth: list[str],
        ground_truth_has_premise: list[bool],
    ) -> None:
        self.input = input
        self.predictions = predictions
        self.ground_truth = ground_truth
        self.ground_truth_has_premise = ground_truth_has_premise

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
            "ground_truth_has_premise": self.ground_truth_has_premise,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> SmallAttempt:
        return cls(
            json_data["input"],
            json_data["predictions"],
            json_data["ground_truth"],
            json_data["ground_truth_has_premise"],
        )

    @classmethod
    def from_attempt_big(cls, attempt: StepAttempt) -> SmallAttempt:
        ground_truth_has_premise = [
            0 < len(s.step_context) for s in attempt.ground_truth
        ]
        ground_truth_strs = [s.step_text for s in attempt.ground_truth]
        return cls(
            attempt.input,
            attempt.predictions,
            ground_truth_strs,
            ground_truth_has_premise,
        )


class FileEvalSmall:
    def __init__(self, file_info: FileInfo, attempts: list[SmallAttempt]) -> None:
        self.file_info = file_info
        self.attempts = attempts

    def correct_at(self, k: int) -> float:
        num_correct = 0
        for attempt in self.attempts:
            num_correct += attempt.is_correct_at_k(k)
        return num_correct / len(self.attempts)

    def correct_at_margin(self, k: int) -> float:
        correct_at = self.correct_at(k)
        return 1.96 * math.sqrt(correct_at * (1 - correct_at) / len(self.attempts))

    def to_json(self) -> Any:
        return {
            "file_info": self.file_info.to_json(),
            "attempts": [a.to_json() for a in self.attempts],
        }

    def save(self, path: str) -> None:
        path_dirname = os.path.dirname(path)
        os.makedirs(path_dirname, exist_ok=True)
        with open(path, "w") as fout:
            fout.write(json.dumps(self.to_json(), indent=2))

    @classmethod
    def from_json(cls, json_data: Any) -> FileEvalSmall:
        file_info = FileInfo.from_json(json_data["file_info"])
        attempts = [SmallAttempt.from_json(a) for a in json_data["attempts"]]
        return cls(file_info, attempts)

    @classmethod
    def load(cls, path: str) -> FileEvalSmall:
        with open(path, "r") as fin:
            json_data = json.load(fin)
            return cls.from_json(json_data)

    @classmethod
    def from_eval_big(cls, file_eval: FileEval) -> FileEvalSmall:
        small_attempts = [
            SmallAttempt.from_attempt_big(a) for a in file_eval.step_attempts
        ]
        return cls(file_eval.file_info, small_attempts)


__ARG = tuple[str, str]


def get_transform_args(root_eval_dir: str) -> list[__ARG]:
    args: list[__ARG] = []
    for eval_dir in os.listdir(root_eval_dir):
        eval_loc = os.path.join(root_eval_dir, eval_dir)
        eval_attempts_loc = os.path.join(eval_loc, ATTEMPTS_NAME)
        for eval_file in os.listdir(eval_attempts_loc):
            args.append((eval_loc, eval_file))
    return args


def get_eval_file(eval_dir: str, file_name: str) -> FileEvalSmall:
    small_eval_loc = os.path.join(eval_dir, SMALL_ATTEMPTS_NAME, file_name)
    if not os.path.exists(small_eval_loc):
        big_eval = FileEval.load(os.path.join(eval_dir, ATTEMPTS_NAME, file_name))
        small_eval = FileEvalSmall.from_eval_big(big_eval)
        small_eval.save(small_eval_loc)
    return FileEvalSmall.load(small_eval_loc)


if __name__ == "__main__":
    parser = argparse.ArgumentParser("Convert step attempts into more compact repr.")
    parser.add_argument(
        "root_eval_dir", help="Location of directory housing all evaluations."
    )
    parser.add_argument(
        "n_procs", type=int, help="Number of processes to help in conversion."
    )
    args = parser.parse_args(sys.argv[1:])
    transform_args = get_transform_args(args.root_eval_dir)
    with multiprocessing.Pool(args.n_procs) as pool:
        pool.starmap(get_eval_file, transform_args)
