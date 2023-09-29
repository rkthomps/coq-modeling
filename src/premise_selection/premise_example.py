
from __future__ import annotations
from typing import Optional, Type, Any
import random
import pdb

from data_management.dataset_file import FocusedStep, Proof, DatasetFile
from premise_selection.premise_formatter import (
    PREMISE_ALIASES, PremiseFormat, CONTEXT_ALIASES, ContextFormat)


class PremiseExample:
    def __init__(self, context: str, premise: str) -> None:
        self.context = context
        self.premise = premise


class PremiseTrainingExample:
    def __init__(self, context: str, 
                 pos_premise: str, 
                 neg_premises: list[str],
                 all_pos_premises: list[str]):
        assert type(context) == str 
        assert type(pos_premise) == str
        assert type(neg_premises) == list 
        assert all([type(p) == str for p in neg_premises])
        assert all([type(p) == str for p in all_pos_premises])
        self.context = context
        self.pos_premise = pos_premise
        self.neg_premises = neg_premises
        self.all_pos_premises = all_pos_premises

    def to_json(self) -> Any:
        return {
            "context": self.context,
            "pos_premise": self.pos_premise,
            "neg_premises": self.neg_premises,
            "all_pos_premises": self.all_pos_premises,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> PremiseTrainingExample:
        context = json_data["context"]
        pos_premise = json_data["pos_premise"]
        neg_premises = json_data["neg_premises"]
        all_pos_premises = json_data["all_pos_premises"]
        return cls(context, pos_premise, neg_premises, all_pos_premises)


    @classmethod
    def from_focused_step(cls, step: FocusedStep, proof: Proof,
                          dataset_file: DatasetFile,
                          total_num_negatives: int,
                          num_in_file_negatives: int,
                          context_format: Type[ContextFormat],
                          premise_format: Type[PremiseFormat],
                          ) -> list[PremiseTrainingExample]:
        pos_prems = [premise_format.format(p) for p in step.step.context]
        in_file_neg_prems: list[str] = []
        out_of_file_neg_prems: list[str] = []
        for premise in dataset_file.avail_premises:
            formatted_prem = premise_format.format(premise)
            if formatted_prem in pos_prems:
                continue
            if premise.file_path == proof.theorem.term.file_path:
                if premise.line >= proof.theorem.term.line:
                    continue
                in_file_neg_prems.append(formatted_prem)
            else:
                out_of_file_neg_prems.append(formatted_prem)
        in_file_negs_to_sample = min(num_in_file_negatives, len(in_file_neg_prems))
        out_of_file_negs_to_sample = total_num_negatives - in_file_negs_to_sample 
        training_examples: list[PremiseTrainingExample] = []
        formatted_context = context_format.format(step, proof)
        for pos_prem in pos_prems:
            in_file_negs_sample = random.sample(in_file_neg_prems, in_file_negs_to_sample) 
            out_of_file_negs_sample = random.sample(out_of_file_neg_prems, out_of_file_negs_to_sample)
            all_negs = in_file_negs_sample + out_of_file_negs_sample
            training_example = cls(formatted_context, pos_prem, all_negs, pos_prems)
            training_examples.append(training_example)
        return training_examples

        
        
            





        
        
        






