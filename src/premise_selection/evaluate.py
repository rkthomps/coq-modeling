from __future__ import annotations
from typing import Type, Iterable, Any


import sys, os
import argparse
import pdb
import json
import re

import torch
from transformers import ByT5Tokenizer, T5EncoderModel
from yaml import load, Loader
from tqdm import tqdm

from typeguard import typechecked

from data_management.split_raw_data import SPLITS
from data_management.dataset_file import DatasetFile, Sentence, data_shape_expected
from premise_selection.model import PremiseRetriever
from model_deployment.premise_model_wrapper import (
    PremiseModelWrapper,
    PremiseServerModelWrapper,
    LocalPremiseModelWrapper,
)


@typechecked
class EvalResult:
    def __init__(self, num_avail_premises: int, hits_on: list[int]) -> None:
        self.num_avail_premises = num_avail_premises
        self.hits_on = hits_on

    def to_json(self) -> Any:
        return {
            "num_avail_premises": self.num_avail_premises,
            "hits_on": self.hits_on,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> EvalResult:
        num_avail_premises = json_data["num_avail_premises"]
        hits_on = json_data["hits_on"]
        return cls(num_avail_premises, hits_on)


@typechecked
class EvalData:
    def __init__(self, num_steps: int, eval_result_list: list[EvalResult]) -> None:
        self.num_steps = num_steps
        self.eval_result_list = eval_result_list

    def precision_at(self, k: int) -> float:
        num_recs = k * len(self.eval_result_list)
        num_relevant_recs = 0
        for eval_result in self.eval_result_list:
            hits_below_k = [h for h in eval_result.hits_on if h <= k]
            num_relevant_recs += len(hits_below_k)
        return num_relevant_recs / num_recs

    def recall_at(self, k: int) -> float:
        num_prems = 0
        num_prems_hit = 0
        for eval_result in self.eval_result_list:
            hits_below_k = [h for h in eval_result.hits_on if h <= k]
            num_prems_hit += len(hits_below_k)
            num_prems += len(eval_result.hits_on)
        return num_prems_hit / num_prems

    def to_json(self) -> Any:
        eval_result_json_list: list[Any] = []
        for eval_result in self.eval_result_list:
            eval_result_json_list.append(eval_result.to_json())
        return {
            "num_steps": self.num_steps,
            "eval_result_list": eval_result_json_list,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> EvalData:
        num_steps = json_data["num_steps"]
        eval_result_data_list = json_data["eval_result_list"]
        eval_result_list: list[EvalResult] = []
        for eval_result_data in eval_result_data_list:
            eval_result = EvalResult.from_json(eval_result_data)
            eval_result_list.append(eval_result)
        return cls(num_steps, eval_result_list)


@typechecked
class Evaluator:
    def __init__(
        self, model_wrapper: PremiseModelWrapper, partitioned_data_loc: str, split: str
    ) -> None:
        assert split in SPLITS
        self.split_loc = os.path.join(partitioned_data_loc, split)
        assert data_shape_expected(self.split_loc)
        self.model_wrapper = model_wrapper
        self.partitioned_data_loc = partitioned_data_loc
        self.split = split

    def run_and_save_evaluation(self, save_loc: str) -> None:
        if os.path.exists(save_loc):
            print(f"{save_loc} exists.", file=sys.stderr)
            exit(1)
        eval_data = self.run_evaluation()
        with open(save_loc, "w") as fout:
            fout.write(json.dumps(eval_data.to_json(), indent=2))

    def run_evaluation(self) -> EvalData:
        """Note that |eval_results| = # steps requiring at least one premise."""
        num_steps = 0
        eval_results: list[EvalResult] = []
        for raw_dataset_file in tqdm(os.listdir(self.split_loc)):
            file_loc = os.path.join(self.split_loc, raw_dataset_file)
            parsed_dataset_file = DatasetFile.from_directory(file_loc)
            for proof in parsed_dataset_file.proofs:
                for step in proof.steps:
                    num_steps += 1
                    filter_result = (
                        self.model_wrapper.premise_filter.get_pos_and_avail_premises(
                            step, proof, parsed_dataset_file
                        )
                    )
                    num_positive_premises = len(filter_result.pos_premises)
                    num_avail_premises = len(filter_result.avail_premises)
                    if (num_positive_premises == 0) or (num_avail_premises == 0):
                        continue
                    ranked_premises_generator = (
                        self.model_wrapper.get_ranked_premise_generator(
                            step, proof, filter_result.avail_premises
                        )
                    )
                    hits_on: list[int] = []
                    premises_to_cover = filter_result.pos_premises
                    for i, premise_rec in enumerate(ranked_premises_generator):
                        if self.attempt_premise_remove(premises_to_cover, premise_rec):
                            hits_on.append(i + 1)
                            if len(premises_to_cover) == 0:
                                break
                    try:
                        assert len(premises_to_cover) == 0
                    except AssertionError:
                        pdb.set_trace()
                    try:
                        assert len(hits_on) == num_positive_premises
                    except AssertionError:
                        pdb.set_trace()
                    eval_results.append(EvalResult(num_avail_premises, hits_on))
        return EvalData(num_steps, eval_results)

    @staticmethod
    def attempt_premise_remove(
        premise_list: list[Sentence], to_remove: Sentence
    ) -> bool:
        try:
            premise_list.remove(to_remove)
            return True
        except ValueError:
            return False


def get_save_loc(checkpoint_loc: str) -> str:
    checkpoint_basename = os.path.basename(args.checkpoint_loc)
    checkpoint_suffix = ".ckpt"
    assert type(checkpoint_basename) == str
    assert checkpoint_basename.endswith(checkpoint_suffix)
    model_loc = PremiseRetriever.get_model_loc(checkpoint_loc)
    save_basename = checkpoint_basename[: (-1 * len(checkpoint_suffix))] + "-eval.json"
    save_loc = os.path.join(model_loc, save_basename)
    return save_loc


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Conduct an evaluation of a premise selection model."
    )
    parser.add_argument("checkpoint_loc", help="Path to model checkpoint to evaluate.")
    parser.add_argument("partitioned_data_loc", help="Location of partioned raw data.")
    parser.add_argument("split", help=f"One of {SPLITS}. Which split to evaluate on")

    args = parser.parse_args(sys.argv[1:])

    # model_wrapper = PremiseServerModelWrapper.from_url("http://127.0.0.1:5000")
    model_wrapper = LocalPremiseModelWrapper.from_checkpoint(args.checkpoint_loc)

    evaluator = Evaluator(model_wrapper, args.partitioned_data_loc, args.split)
    save_loc = get_save_loc(args.checkpoint_loc)
    evaluator.run_and_save_evaluation(save_loc)
