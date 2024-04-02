from __future__ import annotations
from typing import Type, Iterable, Any, Optional


import sys, os
import argparse
import pdb
import json
import re
import logging

import torch
from transformers import ByT5Tokenizer, T5EncoderModel
from yaml import load, Loader
from tqdm import tqdm

from typeguard import typechecked

from data_management.sentence_db import SentenceDB
from data_management.splits import DataSplit, Split, DATA_POINTS_NAME
from data_management.dataset_file import DatasetFile, Sentence, data_shape_expected
from premise_selection.model import PremiseRetriever
from model_deployment.premise_model_wrapper import (
    PremiseModelWrapper,
    PremiseServerModelWrapper,
    LocalPremiseModelWrapper,
    LocalRerankModelWrapper,
    get_ranked_premise_generator,
    move_prem_wrapper_to,
    premise_wrapper_from_conf,
    TFIdf,
    BM25Okapi,
)
from util.util import LOGGER

class EvalResult:
    def __init__(
        self,
        num_avail_premises: int,
        hits_on: list[int],
        num_positive_premises: int,
    ) -> None:
        self.num_avail_premises = num_avail_premises
        self.hits_on = hits_on
        self.num_positive_premises = num_positive_premises

    def to_json(self) -> Any:
        return {
            "num_avail_premises": self.num_avail_premises,
            "hits_on": self.hits_on,
            "num_positive_premises": self.num_positive_premises,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> EvalResult:
        num_avail_premises = json_data["num_avail_premises"]
        hits_on = json_data["hits_on"]
        if "num_positive_premises" in json_data:
            num_positive_premises = json_data["num_positive_premises"]
        else:
            num_positive_premises = len(hits_on)
        return cls(num_avail_premises, hits_on, num_positive_premises)


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
            num_prems += eval_result.num_positive_premises
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


class Evaluator:
    def __init__(
        self,
        model_wrapper: PremiseModelWrapper,
        data_loc: str,
        sentence_db: SentenceDB,
        data_split: DataSplit,
        split: Split,
    ) -> None:
        self.model_wrapper = model_wrapper
        self.data_loc = data_loc
        self.sentence_db = sentence_db
        self.data_split = data_split
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
        for file_info in tqdm(self.data_split.get_file_list(self.split)):
            dset_file = file_info.get_dp(self.data_loc, self.sentence_db)
            for proof in dset_file.proofs:
                for step in proof.steps:
                    num_steps += 1
                    filter_result = (
                        self.model_wrapper.premise_filter.get_pos_and_avail_premises(
                            step, proof, dset_file
                        )
                    )
                    num_positive_premises = len(filter_result.pos_premises)
                    num_avail_premises = len(filter_result.avail_premises)
                    if (num_positive_premises == 0) or (num_avail_premises == 0):
                        continue
                    ranked_premises_generator = get_ranked_premise_generator(
                        self.model_wrapper, step, proof, filter_result.avail_premises
                    )

                    hits_on: list[int] = []
                    premises_to_cover = filter_result.pos_premises
                    for i, premise_rec in enumerate(ranked_premises_generator):
                        if self.attempt_premise_remove(premises_to_cover, premise_rec):
                            hits_on.append(i + 1)
                            if len(premises_to_cover) == 0:
                                break
                    eval_results.append(
                        EvalResult(num_avail_premises, hits_on, num_positive_premises)
                    )
            tmp_data = EvalData(num_steps, eval_results)
            LOGGER.info(
                f"Recalls: @1: {tmp_data.recall_at(1)}; @10: {tmp_data.recall_at(10)}; @100: {tmp_data.recall_at(100)}"
            )
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


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Conduct an evaluation of a premise selection model."
    )
    parser.add_argument("checkpoint_loc", help="Path to model checkpoint to evaluate.")
    parser.add_argument("--vdb", help="Optional location of the vector database")
    parser.add_argument("data_loc", help="Path to dataset.")
    parser.add_argument("sentence_db_loc", help="Path to sentence db")
    parser.add_argument("data_split_loc", help="Path to data split")
    parser.add_argument("save_loc", help="Where to save eval results.")

    args = parser.parse_args(sys.argv[1:])

    if args.checkpoint_loc == TFIdf.ALIAS or args.checkpoint_loc == BM25Okapi.ALIAS:
        model_wrapper = premise_wrapper_from_conf({"alias": args.checkpoint_loc})
    elif "rerank" in args.checkpoint_loc.lower():
        model_wrapper = LocalRerankModelWrapper.from_checkpoint(args.checkpoint_loc)
    else:
        model_wrapper = LocalPremiseModelWrapper.from_checkpoint(args.checkpoint_loc, args.vdb)

    move_prem_wrapper_to(model_wrapper, "cuda")
    sentence_db = SentenceDB.load(args.sentence_db_loc)
    data_split = DataSplit.load(args.data_split_loc)

    evaluator = Evaluator(
        model_wrapper, args.data_loc, sentence_db, data_split, Split.VAL
    )
    evaluator.run_and_save_evaluation(args.save_loc)
