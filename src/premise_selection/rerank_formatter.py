from typing import Any

from premise_selection.rerank_example import RerankExample
from data_management.dataset_file import FocusedStep, Proof, DatasetFile
from model_deployment.premise_model_wrapper import (
    PremiseModelWrapper,
    premise_wrapper_from_conf,
    get_ranked_premise_generator,
    move_prem_wrapper_to,
)


class RerankFormatter:
    ALIAS = "basic"

    def __init__(self, premise_wrapper: PremiseModelWrapper, consider_num: int) -> None:
        self.premise_wrapper = premise_wrapper
        self.consider_num = consider_num

    def examples_from_step(
        self,
        step: FocusedStep,
        proof: Proof,
        dp_obj: DatasetFile,
        skip_no_pos_premises: bool,
    ) -> list[RerankExample]:
        filtered_result = (
            self.premise_wrapper.premise_filter.get_pos_and_avail_premises(
                step, proof, dp_obj
            )
        )
        if skip_no_pos_premises and len(filtered_result.pos_premises) == 0:
            return []
        ranked_premises = get_ranked_premise_generator(
            self.premise_wrapper, step, proof, filtered_result.avail_premises
        )
        formatted_context = self.premise_wrapper.context_format.format(step, proof)
        examples: list[RerankExample] = []
        for i, premise in enumerate(ranked_premises):
            formatted_premise = self.premise_wrapper.premise_format.format(premise)
            if premise in filtered_result.pos_premises:
                examples.append(
                    RerankExample(formatted_premise, formatted_context, True)
                )
            else:
                examples.append(
                    RerankExample(formatted_premise, formatted_context, False)
                )
            if self.consider_num <= i:
                break
        return examples

    def move_to(self, cuda_device: str) -> None:
        move_prem_wrapper_to(self.premise_wrapper, cuda_device)

    @classmethod
    def from_conf(cls, config: Any) -> RerankFormatter:
        premise_wrapper = premise_wrapper_from_conf(config["premise_wrapper"])
        consider_num = config["consider_num"]
        return cls(premise_wrapper, consider_num)
