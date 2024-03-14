from __future__ import annotations
from typing import Optional, Type, Any
import random
import pdb

from typeguard import typechecked


from data_management.splits import Split
from data_management.dataset_file import FocusedStep, Proof, DatasetFile
from premise_selection.premise_formatter import (
    PREMISE_ALIASES,
    PremiseFormat,
    CONTEXT_ALIASES,
    ContextFormat,
)
from premise_selection.premise_filter import PremiseFilter


@typechecked
class ReRankExample:
    def __init__(self, premise: str, context: str, label: bool) -> None:
        self.premise = premise
        self.context = context
        self.label = label

    def to_json(self) -> Any:
        return {
            "premise": self.premise,
            "context": self.context,
            "label": self.label,
        }
    
    @classmethod
    def from_json(cls, json_data: Any) -> ReRankExample:
        premise = json_data["premise"]
        context = json_data["context"]
        label = json_data["label"]
        return cls(premise, context, label)
    


@typechecked
class PremiseTrainingExample:
    def __init__(
        self,
        context: str,
        pos_premise: str,
        neg_premises: list[str],
        all_pos_premises: list[str],
    ):
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
    def from_focused_step(
        cls,
        step: FocusedStep,
        proof: Proof,
        dataset_file: DatasetFile,
        total_num_negatives: int,
        num_in_file_negatives: int,
        context_format: Type[ContextFormat],
        premise_format: Type[PremiseFormat],
        premise_filter: PremiseFilter,
        split: Split,
    ) -> list[PremiseTrainingExample]:
        in_file_neg_prems: list[str] = []
        out_of_file_neg_prems: list[str] = []
        filter_result = premise_filter.get_pos_and_avail_premises(
            step, proof, dataset_file
        )
        formatted_pos_prems = [
            premise_format.format(p) for p in filter_result.pos_premises
        ]
        for premise in filter_result.avail_premises:
            formatted_prem = premise_format.format(premise)
            if formatted_prem in formatted_pos_prems:
                continue
            if premise.file_path == proof.theorem.term.file_path:
                in_file_neg_prems.append(
                    formatted_prem
                )  # filtering done by premisefilter
            else:
                out_of_file_neg_prems.append(formatted_prem)

        if len(in_file_neg_prems) + len(out_of_file_neg_prems) < total_num_negatives:
            return []
        if len(out_of_file_neg_prems) < total_num_negatives:
            out_of_file_negs_to_sample = len(out_of_file_neg_prems)
            in_file_negs_to_sample = total_num_negatives - out_of_file_negs_to_sample
        else:
            in_file_negs_to_sample = min(num_in_file_negatives, len(in_file_neg_prems))
            out_of_file_negs_to_sample = total_num_negatives - in_file_negs_to_sample

        in_file_negs_to_sample = min(num_in_file_negatives, len(in_file_neg_prems))
        out_of_file_negs_to_sample = total_num_negatives - in_file_negs_to_sample
        if out_of_file_negs_to_sample > len(out_of_file_neg_prems):
            return []
        training_examples: list[PremiseTrainingExample] = []
        formatted_context = context_format.format(step, proof)
        for pos_prem in formatted_pos_prems:
            in_file_negs_sample = random.sample(
                in_file_neg_prems, in_file_negs_to_sample
            )
            out_of_file_negs_sample = random.sample(
                out_of_file_neg_prems, out_of_file_negs_to_sample
            )
            all_negs = in_file_negs_sample + out_of_file_negs_sample
            training_example = cls(
                formatted_context, pos_prem, all_negs, formatted_pos_prems
            )
            training_examples.append(training_example)
        return training_examples
