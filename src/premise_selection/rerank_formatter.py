from __future__ import annotations
from typing import Any
import random

from premise_selection.rerank_example import RerankExample
from data_management.dataset_file import FocusedStep, Proof, DatasetFile, Sentence
from model_deployment.premise_model_wrapper import (
    PremiseModelWrapper,
    premise_wrapper_from_conf,
    get_ranked_premise_generator,
    move_prem_wrapper_to,
)


class RerankFormatter:
    ALIAS = "basic"

    def __init__(
        self,
        premise_wrapper: PremiseModelWrapper,
        consider_num: int,
        negatives_per_positive: int,
    ) -> None:
        self.premise_wrapper = premise_wrapper
        self.consider_num = consider_num
        self.negatives_per_positive = negatives_per_positive

    def examples_from_step(
        self,
        step: FocusedStep,
        proof: Proof,
        dp_obj: DatasetFile,
    ) -> list[RerankExample]:
        filtered_result = (
            self.premise_wrapper.premise_filter.get_pos_and_avail_premises(
                step, proof, dp_obj
            )
        )
        ranked_premises = get_ranked_premise_generator(
            self.premise_wrapper, step, proof, filtered_result.avail_premises
        )
        formatted_context = self.premise_wrapper.context_format.format(step, proof)

        negative_premise_bank: list[Sentence] = []
        for i, premise in enumerate(ranked_premises):
            if self.consider_num <= i:
                break
            if premise in filtered_result.pos_premises:
                continue
            negative_premise_bank.append(premise)

        examples: list[RerankExample] = []
        for pos_premise in filtered_result.pos_premises:
            formatted_pos_premise = self.premise_wrapper.premise_format.format(
                pos_premise
            )
            examples.append(
                RerankExample(formatted_pos_premise, formatted_context, True)
            )
            if len(negative_premise_bank) < self.negatives_per_positive:
                negatives = negative_premise_bank
            else:
                negatives = random.sample(
                    negative_premise_bank, self.negatives_per_positive
                )
            for negative in negatives:
                formatted_neg_premise = self.premise_wrapper.premise_format.format(
                    negative
                )
                examples.append(
                    RerankExample(formatted_neg_premise, formatted_context, False)
                )
        return examples

    def move_to(self, cuda_device: str) -> None:
        move_prem_wrapper_to(self.premise_wrapper, cuda_device)

    @classmethod
    def from_conf(cls, config: Any) -> RerankFormatter:
        premise_wrapper = premise_wrapper_from_conf(config["premise_wrapper"])
        consider_num = config["consider_num"]
        negatives_per_positive = config["negatives_per_positive"]
        return cls(premise_wrapper, consider_num, negatives_per_positive)
