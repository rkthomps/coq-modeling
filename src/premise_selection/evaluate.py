from __future__ import annotations
from typing import Type, Iterable, Any, Optional


import sys, os
import time
import pickle
import json
from pathlib import Path

from dataclasses import dataclass

from tqdm import tqdm

from data_management.dataset_file import Sentence
from data_management.sentence_db import SentenceDB
from data_management.splits import DataSplit, Split, str2split
from model_deployment.premise_client import (
    PremiseConf,
    PremiseClient,
    SelectPremiseClient,
    premise_client_from_conf,
    premise_conf_from_yaml,
    get_dependency_examples,
)
from util.util import get_basic_logger
from util.constants import CLEAN_CONFIG

_logger = get_basic_logger(__name__)


@dataclass
class PremiseEvalConf:
    premise_conf: PremiseConf
    data_loc: Path
    sentence_db_loc: Path
    data_split_loc: Path
    split_name: str
    save_loc: Path

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> PremiseEvalConf:
        return cls(
            premise_conf_from_yaml(yaml_data["premise"]),
            Path(yaml_data["data_loc"]),
            Path(yaml_data["sentence_db_loc"]),
            Path(yaml_data["data_split_loc"]),
            yaml_data["split_name"],
            Path(yaml_data["save_loc"]),
        )


@dataclass
class EvalResult:
    num_avail_premises: int
    hits_on: list[int]
    num_positive_premises: int

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


@dataclass
class EvalData:
    num_steps: int
    eval_result_list: list[EvalResult]

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


def run_and_save_evaluation(eval_conf: PremiseEvalConf) -> None:
    if eval_conf.save_loc.exists():
        print(f"{eval_conf.save_loc} exists.", file=sys.stderr)
        exit(1)
    eval_data = run_evaluation(eval_conf)
    with eval_conf.save_loc.open("w") as fout:
        fout.write(json.dumps(eval_data.to_json(), indent=2))


def run_evaluation(eval_conf: PremiseEvalConf) -> EvalData:
    """Note that |eval_results| = # steps requiring at least one premise."""
    num_steps = 0
    eval_results: list[EvalResult] = []
    data_split = DataSplit.load(eval_conf.data_split_loc)
    sentence_db = SentenceDB.load(eval_conf.sentence_db_loc)
    split = str2split(eval_conf.split_name)
    premise_client = premise_client_from_conf(eval_conf.premise_conf)
    for file_info in tqdm(data_split.get_file_list(split)):
        dset_file = file_info.get_dp(eval_conf.data_loc, sentence_db)
        for i, proof in enumerate(dset_file.proofs):
            # if isinstance(premise_client, SelectPremiseClient):
            #     print("Setting transformation matrix...", end="")
            #     s = time.time()
            #     premise_examples, step_examples, proof_examples = (
            #         get_dependency_examples(
            #             i,
            #             dset_file,
            #             eval_conf.data_loc,
            #             sentence_db,
            #             premise_client.premise_filter,
            #         )
            #     )
            #     print("num examples:", len(premise_examples))
            #     e = time.time()
            #     premise_client.clear_transformation_matrix()
            #     premise_client.set_transformation_matrix(
            #         premise_examples, step_examples, proof_examples
            #     )
            #     print(e - s)
            for step in proof.steps:
                num_steps += 1
                filter_result = (
                    premise_client.premise_filter.get_pos_and_avail_premises(
                        step, proof, dset_file
                    )
                )
                num_positive_premises = len(filter_result.pos_premises)
                num_avail_premises = len(filter_result.avail_premises)
                if (num_positive_premises == 0) or (num_avail_premises == 0):
                    continue
                ranked_premises_generator = premise_client.get_ranked_premise_generator(
                    step, proof, filter_result.avail_premises
                )

                hits_on: list[int] = []
                premises_to_cover = filter_result.pos_premises
                for i, premise_rec in enumerate(ranked_premises_generator):
                    if attempt_premise_remove(premises_to_cover, premise_rec):
                        hits_on.append(i + 1)
                        if len(premises_to_cover) == 0:
                            break
                eval_results.append(
                    EvalResult(num_avail_premises, hits_on, num_positive_premises)
                )
        tmp_data = EvalData(num_steps, eval_results)
        print(
            f"Recalls: @1: {tmp_data.recall_at(1)}; @10: {tmp_data.recall_at(10)}; @100: {tmp_data.recall_at(100)}"
        )
    return EvalData(num_steps, eval_results)


def attempt_premise_remove(premise_list: list[Sentence], to_remove: Sentence) -> bool:
    try:
        premise_list.remove(to_remove)
        return True
    except ValueError:
        return False


if __name__ == "__main__":
    conf_loc = Path(f"./{CLEAN_CONFIG}")
    with conf_loc.open("rb") as fin:
        eval_config: PremiseEvalConf = pickle.load(fin)

    run_and_save_evaluation(eval_config)
