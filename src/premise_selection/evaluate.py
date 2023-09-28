
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


from data_management.split_raw_data import SPLITS
from data_management.split_raw_data import data_shape_expected
from data_management.dataset_file import DatasetFile, Sentence
from premise_selection.model import PremiseRetriever 
from premise_selection.premise_formatter import (PremiseFormat, ContextFormat, 
                                                 PREMISE_ALIASES, CONTEXT_ALIASES)
from premise_selection.datamodule import tokenize_strings 

class EvalResult:
    def __init__(self, num_premises: int, 
                 hits_on: list[int]) -> None:
        """
        num_recs_required: number of recommendations required
          before all ground truth recommendations were recommended
        """
        assert type(num_premises) == int
        assert type(hits_on) == list
        assert all([type(h) == int for h in hits_on])
        self.num_premises = num_premises
        self.hits_on = hits_on


    def to_json(self) -> Any:
        return {
            "num_premises": self.num_premises,
            "hits_on": self.hits_on,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> EvalResult:
        num_premises = json_data["num_premises"]
        hits_on = json_data["hits_on"]
        return cls(num_premises, hits_on)


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
    


class Evaluator:
    def __init__(self, model_loc: str,
                 checkpoint_name: str,
                 partitioned_data_loc: str,
                 split: str,
                 premise_format: Type[PremiseFormat],
                 context_format: Type[ContextFormat]) -> None:
        assert type(model_loc) == str
        assert type(checkpoint_name) == str
        assert type(partitioned_data_loc) == str
        assert type(split) == str
        assert split in SPLITS
        split_loc = os.path.join(partitioned_data_loc, split)
        assert data_shape_expected(split_loc)
        self.model_loc = model_loc
        self.checkpoint_name = checkpoint_name
        self.model = PremiseRetriever.load_from_conf_and_checkpoint(
            self.model_loc, self.checkpoint_name)
        self.partitioned_data_loc = partitioned_data_loc
        self.split = split
        self.embedding_cache: dict[str, torch.Tensor] = {}
        self.split_loc = os.path.join(partitioned_data_loc, split)
        self.premise_format = premise_format
        self.context_format = context_format

    
    def __get_embedding(self, to_embed: str) -> torch.Tensor:
        if to_embed in self.embedding_cache:
            return self.embedding_cache[to_embed]
        encoding = self.model.encode_str(to_embed)
        self.embedding_cache[to_embed] = encoding
        return encoding 


    def __get_ranked_premises(self, context: str, premises: list[Sentence]) -> Iterable[Sentence]:
        context_embedding = self.__get_embedding(context) 
        prem_embeddings: list[torch.Tensor] = []
        for prem in premises:
            formatted_prem = self.premise_format.format(prem)
            prem_embeddings.append(self.__get_embedding(formatted_prem)) 
        all_prem_embeddings = torch.cat(prem_embeddings)
        scores = torch.mm(context_embedding, all_prem_embeddings.t())
        flat_scores = scores.squeeze()
        assert flat_scores.ndim == 1
        sentence_order = list(torch.argsort(flat_scores, descending=True))
        for idx in sentence_order:
            yield premises[idx]


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
                    formatted_context = self.context_format.format(step, proof)
                    premises_to_cover = self.get_only_past_prems(
                        step.step.context, proof.theorem.term, parsed_dataset_file.avail_premises)
                    num_premises = len(premises_to_cover)
                    if num_premises == 0:
                        continue
                    premises_available = parsed_dataset_file.get_premises_before(proof)
                    assert len(premises_available) > 0
                    ranked_premises_generator = self.__get_ranked_premises(
                        formatted_context, premises_available)
                    hits_on: list[int] = []
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
                        assert len(hits_on) == num_premises
                    except AssertionError:
                        pdb.set_trace()
                    eval_results.append(EvalResult(num_premises, hits_on))
        return EvalData(num_steps, eval_results)


    @staticmethod
    def attempt_premise_remove(premise_list: list[Sentence], to_remove: Sentence) -> bool:
        try:
            premise_list.remove(to_remove)
            return True
        except ValueError:
            return False


    @staticmethod
    def get_only_past_prems(premise_list: list[Sentence], 
                            proof_term: Sentence, 
                            all_premises: list[Sentence]) -> list[Sentence]:
        only_before: list[Sentence] = []
        for premise in premise_list:
            if premise not in all_premises:
                print(f"Premise at {premise.file_path}:{premise.line} not found in any of the available prems for {proof_term.file_path}")
                continue
            if premise.file_path != proof_term.file_path:
                only_before.append(premise)
                continue
            if premise.line < proof_term.line:
                only_before.append(premise)
                continue
            if premise == proof_term:
                print(f"Found self referenceing premise in {premise.file_path} at line {premise.line}.")
            elif premise.line > proof_term.line:
                print(f"Found forward referenceing premise in {premise.file_path} at line {premise.line}")
            else:
                raise ValueError(f"Found non-equal premise at same line as term at {premise.file_path} at line {premise.line}")
        return only_before



            
            


def checkpoint_base(checkpoint_name: str) -> str:
    ending = ".ckpt" 
    assert checkpoint_name.endswith(ending)
    return checkpoint_name[:(-1 * len(ending))]
    

if __name__=="__main__":
    parser = argparse.ArgumentParser(
        description="Conduct an evaluation of a premise selection model.")
    parser.add_argument("model_loc",
                        help="Location of the model to evaluate.")
    parser.add_argument("checkpoint_name",
                        help="Name of checkpoint to use to load the model.")
    parser.add_argument("split",
                        help=f"One of {SPLITS}. Which split to evaluate on")
    parser.add_argument("premise_data_config",
                        help=("Location of config saved in the directory of the "
                              "premise selection dataset."))
    args = parser.parse_args(sys.argv[1:])

    checkpoint_base_name = checkpoint_base(args.checkpoint_name)
    save_loc = os.path.join(args.model_loc, checkpoint_base_name + "-eval.json")

    with open(args.premise_data_config, "r") as fin:
        conf = load(fin, Loader=Loader) 

    partitioned_data_loc = conf["partitioned_data_loc"]
    premise_format = PREMISE_ALIASES[conf["premise_format_alias"]]
    context_format = CONTEXT_ALIASES[conf["context_format_alias"]]

    evaluator = Evaluator(
        args.model_loc,
        args.checkpoint_name,
        partitioned_data_loc,
        args.split,
        premise_format,
        context_format
    )

    evaluator.run_and_save_evaluation(save_loc)

            
                    