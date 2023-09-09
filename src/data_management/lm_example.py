from __future__ import annotations
from typing import Any

import sys, os
import pdb
import jsonlines

from data_management.dataset_file import (
    DatasetFile, FocusedStep, Proof)


class LmExample:
    def __init__(self, input: str, output: str) -> None:
        assert type(input) == str
        assert type(output) == str
        self.input = input
        self.output = output

    def to_json(self) -> dict[str, str]:
        return {
            "input": self.input,
            "output": self.output,
        }

    @classmethod
    def json_from_dataset_file(cls, dataset_file: DatasetFile) -> list[dict[str, str]]:
        return [example.to_json() for example in cls.from_dataset_file(dataset_file)]

    @classmethod
    def from_dataset_file(cls, dataset_file: DatasetFile) -> list[LmExample]:
        raise NotImplementedError

    @classmethod
    def from_json(cls, json_data: Any) -> LmExample:
        input = json_data["input"]
        output = json_data["output"]
        return cls(input, output)



class BasicLmExample(LmExample):
    def __init__(self, input: str, output: str) -> None:
        super(BasicLmExample, self).__init__(input, output)

    @classmethod
    def __example_from_step(cls, step: FocusedStep, proof: Proof) -> BasicLmExample:
        goal_strings: list[str] = []
        for goal in step.goals:
            goal_strings.append(goal.to_string())
        partial_proof_string = proof.proof_prefix_to_string(step)
        final_goal_string = "<GOAL-SEP>".join(goal_strings)
        input = f"{partial_proof_string}<THM-SEP>{final_goal_string}"
        output = step.step.text
        return cls(input, output)

    @classmethod
    def from_dataset_file(cls, dataset_file: DatasetFile) -> list[LmExample]:
        basic_lm_examples: list[LmExample] = []
        for proof in dataset_file.proofs:
            for step in proof.steps:
                basic_lm_examples.append(cls.__example_from_step(step, proof))
        return basic_lm_examples



if __name__ == "__main__":
    TEST_PATH = "/Users/kylethompson/UCSD/llm-difference-descriptions/coq-lsp-mining/res/"
    all_examples: list[LmExample] = []
    for dirname in os.listdir(TEST_PATH):
        absolute_dirname = os.path.join(TEST_PATH, dirname)
        obj = DatasetFile.from_directory(absolute_dirname)
        examples = BasicLmExample.from_dataset_file(obj)
        all_examples.extend(examples)

    with jsonlines.open("test_examples.jsonl", "w") as fout:
        fout.write_all([e.to_json() for e in all_examples])

                

