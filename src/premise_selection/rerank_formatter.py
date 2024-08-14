from __future__ import annotations
from typing import Any
import random
from dataclasses import dataclass

from premise_selection.rerank_example import RerankExample
from data_management.dataset_file import FocusedStep, Proof, DatasetFile, Sentence
from premise_selection.premise_client import (
    SelectClient,
    SelectClientConf,
    select_client_from_conf,
    select_conf_from_yaml,
)


@dataclass
class BasicRerankFormatterConf:
    ALIAS = "basic"
    select_conf: SelectClientConf
    consider_num: int
    negatives_per_positive: int

    def __hash__(self) -> int:
        return hash(str(self))

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> BasicRerankFormatterConf:
        premise_conf = select_conf_from_yaml(yaml_data["select_conf"])
        consider_num = yaml_data["consider_num"]
        negatives_per_positive = yaml_data["negatives_per_positive"]
        return cls(premise_conf, consider_num, negatives_per_positive)


# @dataclass
# class ProofRerankFormatterConf:
#     ALIAS = "proof"
#     select_conf: SelectClientConf
#     proof_retriever: TfIdfProofRetrieverConf
#     consider_num: int
#     include_proofs_num: int
#     negatives_per_positive: int

#     def __hash__(self) -> int:
#         return hash(str(self))

#     @classmethod
#     def from_yaml(cls, yaml_data: Any) -> ProofRerankFormatterConf:
#         return cls(
#             select_conf_from_yaml(yaml_data["select_conf"]),
#             TfIdfProofRetrieverConf.from_yaml(yaml_data["text_proof_retriever"]),
#             yaml_data["consider_num"],
#             yaml_data["include_proofs_num"],
#             yaml_data["negatives_per_positive"],
#         )


RerankFormatterConf = BasicRerankFormatterConf


def rerank_conf_from_yaml(yaml_data: Any) -> RerankFormatterConf:
    attempted_alias = yaml_data["alias"]
    match attempted_alias:
        case BasicRerankFormatterConf.ALIAS:
            return BasicRerankFormatterConf.from_yaml(yaml_data)
        case _:
            raise ValueError(f"Rerank conf not found: {attempted_alias}.")


class BasicRerankFormatter:
    def __init__(
        self,
        premise_client: SelectClient,
        consider_num: int,
        negatives_per_positive: int,
    ) -> None:
        self.premise_client = premise_client
        self.consider_num = consider_num
        self.negatives_per_positive = negatives_per_positive

    def get_formatted_context(
        self, step: FocusedStep, proof: Proof, dp_obj: DatasetFile
    ) -> str:
        formatted_context = self.premise_client.context_format.format(step, proof)
        return formatted_context

    def examples_from_step(
        self,
        step: FocusedStep,
        proof: Proof,
        dp_obj: DatasetFile,
    ) -> list[RerankExample]:
        filtered_result = self.premise_client.premise_filter.get_pos_and_avail_premises(
            step, proof, dp_obj
        )
        ranked_premises = self.premise_client.get_ranked_premises(
            step, proof, dp_obj, filtered_result.avail_premises
        )
        formatted_context = self.get_formatted_context(step, proof, dp_obj)

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
    def from_conf(cls, conf: BasicRerankFormatterConf) -> BasicRerankFormatter:
        premise_client = select_client_from_conf(conf.select_conf)
        return cls(premise_client, conf.consider_num, conf.negatives_per_positive)


# class ProofRerankFormatter:
#     def __init__(
#         self,
#         premise_client: SelectClient,
#         proof_retriever: TfIdfProofRetriever,
#         include_proofs_num: int,
#         consider_num: int,
#         negatives_per_positive: int,
#     ):
#         self.premise_client = premise_client
#         self.proof_retriever = proof_retriever
#         self.include_proofs_num = include_proofs_num
#         self.consider_num = consider_num
#         self.negatives_per_positive = negatives_per_positive

#     def get_formatted_context(
#         self, step: FocusedStep, proof: Proof, dp_obj: DatasetFile
#     ) -> str:
#         all_top_proofs = self.proof_retriever.get_similar_proofs(step, proof, dp_obj)
#         top_proofs = all_top_proofs[: self.include_proofs_num][
#             ::-1
#         ]  # want closest proofs last
#         top_proofs_str = "\n".join([p.proof_text_to_string() for p in top_proofs])
#         formatted_context = self.premise_client.context_format.format(step, proof)
#         proof_formatted_context = top_proofs_str + "\n\n" + formatted_context
#         return proof_formatted_context

#     def examples_from_step(
#         self,
#         step: FocusedStep,
#         proof: Proof,
#         dp_obj: DatasetFile,
#     ) -> list[RerankExample]:
#         filtered_result = self.premise_client.premise_filter.get_pos_and_avail_premises(
#             step, proof, dp_obj
#         )
#         ranked_premises = self.premise_client.get_ranked_premise_generator(
#             step, proof, dp_obj, filtered_result.avail_premises
#         )

#         negative_premise_bank: list[Sentence] = []
#         for i, premise in enumerate(ranked_premises):
#             if self.consider_num <= i:
#                 break
#             if premise in filtered_result.pos_premises:
#                 continue
#             negative_premise_bank.append(premise)

#         examples: list[RerankExample] = []
#         proof_formatted_context = self.get_formatted_context(step, proof, dp_obj)
#         for pos_premise in filtered_result.pos_premises:
#             formatted_pos_premise = self.premise_client.premise_format.format(
#                 pos_premise
#             )
#             examples.append(
#                 RerankExample(formatted_pos_premise, proof_formatted_context, True)
#             )
#             if len(negative_premise_bank) < self.negatives_per_positive:
#                 negatives = negative_premise_bank
#             else:
#                 negatives = random.sample(
#                     negative_premise_bank, self.negatives_per_positive
#                 )
#             for negative in negatives:
#                 formatted_neg_premise = self.premise_client.premise_format.format(
#                     negative
#                 )
#                 examples.append(
#                     RerankExample(formatted_neg_premise, proof_formatted_context, False)
#                 )
#         return examples

#     @classmethod
#     def from_conf(cls, conf: ProofRerankFormatterConf) -> ProofRerankFormatter:
#         return cls(
#             select_client_from_conf(conf.select_conf),
#             TfIdfProofRetriever.from_conf(conf.proof_retriever),
#             conf.consider_num,
#             conf.include_proofs_num,
#             conf.negatives_per_positive,
#         )


RerankFormatter = BasicRerankFormatter


def rerank_formatter_from_conf(conf: RerankFormatterConf) -> RerankFormatter:
    match conf:
        case BasicRerankFormatterConf():
            return BasicRerankFormatter.from_conf(conf)


def close_rerank_formatter(f: RerankFormatter):
    match f:
        case BasicRerankFormatter():
            pass
