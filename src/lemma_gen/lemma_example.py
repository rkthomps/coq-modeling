from __future__ import annotations
from typing import Optional, Any
from dataclasses import dataclass

from data_management.dataset_file import DatasetFile, Proof, Goal
from tactic_gen.lm_example import GOAL_SEP, fmt_goals

from premise_selection.premise_filter import PremiseFilter, PremiseFilterConf
from premise_selection.rerank_client import (
    PremiseConf,
    PremiseClient,
    premise_client_from_conf,
    premise_conf_from_yaml,
    close_premise_client,
)

from util.constants import RANGO_LOGGER
import logging

_logger = logging.getLogger(RANGO_LOGGER)


@dataclass
class LemmaExample:
    target: str
    current_state: str
    current_script: str
    relevant_lemmas: Optional[list[str]]

    def to_json(self) -> Any:
        return {
            "target": self.target,
            "current_state": self.current_state,
            "current_script": self.current_script,
            "relevant_lemmas": self.relevant_lemmas,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> LemmaExample:
        return cls(
            json_data["target"],
            json_data["current_state"],
            json_data["current_script"],
            json_data["relevant_lemmas"],
        )


@dataclass
class LemmaFormatterConf:
    premise_filter_conf: PremiseFilterConf
    premise_conf: Optional[PremiseConf]
    max_num_premises: Optional[int]

    def __hash__(self) -> int:
        return hash(str(self))

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> LemmaFormatterConf:
        premise_conf = None
        if "premise" in yaml_data:
            premise_conf = premise_conf_from_yaml(yaml_data["premise"])
        max_num_premises = yaml_data.get("max_num_premises", None)
        if premise_conf is not None:
            assert max_num_premises is not None
        return cls(
            PremiseFilterConf.from_yaml(yaml_data["premise_filter"]),
            premise_conf,
            max_num_premises,
        )


@dataclass
class LemmaFormatter:
    premise_filter: PremiseFilter
    premise_client: Optional[PremiseClient]
    max_num_premises: Optional[int]

    def examples_from_step(
        self,
        step_idx: int,
        proof: Proof,
        dp_obj: DatasetFile,
        training: bool = False,
    ) -> list[LemmaExample]:
        step = proof.steps[step_idx]
        filtered_result = self.premise_filter.get_pos_and_avail_premises(
            step, proof, dp_obj
        )
        examples: list[LemmaExample] = []
        avail_prems = filtered_result.avail_premises
        for pos_prem in filtered_result.pos_premises:
            avail_prems_copy = avail_prems.copy()
            if pos_prem not in avail_prems:
                raise ValueError("Positive premise not in available premises")
            avail_prems_copy.remove(pos_prem)
            if self.premise_client is not None:
                assert self.max_num_premises is not None
                relevant_lemmas = self.premise_client.get_ranked_premises(
                    step_idx, proof, dp_obj, avail_prems_copy, training
                )
                relevant_lemma_texts = [l.text for l in relevant_lemmas]
            else:
                relevant_lemma_texts = None
            script = proof.proof_prefix_to_string(step)
            goals = fmt_goals(step.goals)
            target = pos_prem.text
            example = LemmaExample(target, goals, script, relevant_lemma_texts)
            examples.append(example)
        return examples

    def close(self) -> None:
        if self.premise_client is not None:
            close_premise_client(self.premise_client)

    @classmethod
    def from_conf(cls, conf: LemmaFormatterConf) -> LemmaFormatter:
        premise_conf = None
        premise_formatter = PremiseFilter.from_conf(conf.premise_filter_conf)
        if conf.premise_conf is not None:
            premise_conf = premise_client_from_conf(conf.premise_conf)
        return cls(
            premise_formatter,
            premise_conf,
            conf.max_num_premises,
        )
