from __future__ import annotations
from typing import Any
from typeguard import typechecked

from data_management.dataset_file import FocusedStep, Proof, DatasetFile
from model_deployment.premise_model_wrapper import (
    PremiseModelWrapper,
    premise_wrapper_from_conf,
    get_ranked_premise_generator,
    move_prem_wrapper_to,
)


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


class ReRankFormatter:
    ALIAS = "basic"

    def __init__(self, premise_wrapper: PremiseModelWrapper, consider_num: int) -> None:
        self.premise_wrapper = premise_wrapper
        self.consider_num = consider_num

    def examples_from_step(
        self, step: FocusedStep, proof: Proof, dp_obj: DatasetFile
    ) -> list[ReRankExample]:
        filtered_result = (
            self.premise_wrapper.premise_filter.get_pos_and_avail_premises(
                step, proof, dp_obj
            )
        )
        ranked_premises = get_ranked_premise_generator(
            self.premise_wrapper, step, proof, filtered_result.avail_premises
        )
        formatted_context = self.premise_wrapper.context_format.format(step, proof)
        examples: list[ReRankExample] = []
        for i, premise in enumerate(ranked_premises):
            formatted_premise = self.premise_wrapper.premise_format.format(premise)
            if premise in filtered_result.pos_premises:
                examples.append(
                    ReRankExample(formatted_premise, formatted_context, True)
                )
            else:
                examples.append(
                    ReRankExample(formatted_premise, formatted_context, False)
                )
            if self.consider_num <= i:
                break
        return examples
    
    def move_to(self, cuda_device: str) -> None:
        move_prem_wrapper_to(self.premise_wrapper, cuda_device)

 
    @classmethod
    def from_conf(cls, config: Any) -> ReRankFormatter:
        premise_wrapper = premise_wrapper_from_conf(config["premise_wrapper"])
        consider_num = config["consider_num"]
        return cls(premise_wrapper, consider_num)
