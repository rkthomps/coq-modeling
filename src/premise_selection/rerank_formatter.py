from __future__ import annotations
from typing import Any
import random
from dataclasses import dataclass

from premise_selection.rerank_example import RerankExample
from data_management.dataset_file import FocusedStep, Proof, DatasetFile, Sentence
from model_deployment.premise_client import (
    PremiseConf,
    PremiseClient,
    premise_client_from_conf,
    premise_conf_from_yaml,
)


@dataclass
class RerankFormatterConf:
    ALIAS = "basic"
    premise_conf: PremiseConf
    consider_num: int
    negatives_per_positive: int

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> RerankFormatterConf:
        premise_conf = premise_conf_from_yaml(yaml_data)
        consider_num = yaml_data["consider_num"]
        negatives_per_positive = yaml_data["negatives_per_positive"]
        return cls(premise_conf, consider_num, negatives_per_positive)


class RerankFormatter:
    def __init__(
        self,
        premise_client: PremiseClient,
        consider_num: int,
        negatives_per_positive: int,
    ) -> None:
        self.premise_client = premise_client
        self.consider_num = consider_num
        self.negatives_per_positive = negatives_per_positive

    def examples_from_step(
        self,
        step: FocusedStep,
        proof: Proof,
        dp_obj: DatasetFile,
    ) -> list[RerankExample]:
        filtered_result = self.premise_client.premise_filter.get_pos_and_avail_premises(
            step, proof, dp_obj
        )
        ranked_premises = self.premise_client.get_ranked_premise_generator(
            step, proof, filtered_result.avail_premises
        )
        formatted_context = self.premise_client.context_format.format(step, proof)

        negative_premise_bank: list[Sentence] = []
        for i, premise in enumerate(ranked_premises):
            if self.consider_num <= i:
                break
            if premise in filtered_result.pos_premises:
                continue
            negative_premise_bank.append(premise)

        examples: list[RerankExample] = []
        for pos_premise in filtered_result.pos_premises:
            formatted_pos_premise = self.premise_client.premise_format.format(
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
                formatted_neg_premise = self.premise_client.premise_format.format(
                    negative
                )
                examples.append(
                    RerankExample(formatted_neg_premise, formatted_context, False)
                )
        return examples

    @classmethod
    def from_conf(cls, conf: RerankFormatterConf) -> RerankFormatter:
        premise_client = premise_client_from_conf(conf.premise_conf)
        return cls(premise_client, conf.consider_num, conf.negatives_per_positive)
