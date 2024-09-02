from __future__ import annotations
from typing import Any, Optional
import ipdb

from dataclasses import dataclass

import sys, os

from data_management.dataset_file import DatasetFile, Proof, FocusedStep, Sentence
from coqpyt.coq.structs import TermType

from util.constants import RANGO_LOGGER
import logging

_logger = logging.getLogger(RANGO_LOGGER)


@dataclass
class PremiseFilterConf:
    coq_excludes: list[str]
    non_coq_excludes: list[str]
    general_excludes: list[str]

    def __hash__(self) -> int:
        return hash(
            (
                tuple(self.coq_excludes),
                tuple(self.non_coq_excludes),
                tuple(self.general_excludes),
            )
        )

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> PremiseFilterConf:
        return cls(
            yaml_data["coq_excludes"],
            yaml_data["non_coq_excludes"],
            yaml_data["general_excludes"],
        )


@dataclass
class FilteredResult:
    pos_premises: list[Sentence]
    avail_premises: list[Sentence]


@dataclass
class OOFCache:
    dset_file: DatasetFile
    filtered_list: list[Sentence]
    filtered_set: set[Sentence]


class PremiseFilter:
    def __init__(
        self,
        coq_excludes: list[TermType] = [],
        non_coq_excludes: list[TermType] = [],
        general_excludes: list[TermType] = [],
    ) -> None:
        self.coq_excludes = coq_excludes
        self.non_coq_excludes = non_coq_excludes
        self.general_excludes = general_excludes
        # self.__print_warnings()
        self.__oof_cache: Optional[OOFCache] = None

    def __print_warnings(self) -> None:
        if len(self.coq_excludes) > 0:
            _logger.info(
                (
                    f"Excluding term types {self.coq_excludes} for premise selection "
                    "if they come from the coq standard library."
                )
            )
        if len(self.non_coq_excludes) > 0:
            _logger.info(
                f"Excluding term types {self.non_coq_excludes} for premise selection "
                "if they do not come from the coq standard library."
            )
        if len(self.general_excludes) > 0:
            _logger.info(
                f"Excluding term types {self.non_coq_excludes} for premise selection."
            )

    def filter_premise(self, premise: Sentence) -> bool:
        if premise.sentence_type in self.general_excludes:
            return False
        from_coq = os.path.join("lib", "coq", "theories") in premise.file_path
        if from_coq and (premise.sentence_type in self.coq_excludes):
            return False
        if (not from_coq) and (premise.sentence_type in self.non_coq_excludes):
            return False
        return True

    def get_in_file_filtered_premises(
        self, step: FocusedStep, proof: Proof, dset_obj: DatasetFile
    ) -> list[Sentence]:
        in_file_before_proof = dset_obj.get_in_file_premises_before(proof)
        return [p for p in in_file_before_proof if self.filter_premise(p)]

    def __check_dset_cache(self, dset_obj: DatasetFile) -> OOFCache:
        match self.__oof_cache:
            case OOFCache(dset_file=cache_dset_file) if cache_dset_file is dset_obj:
                return self.__oof_cache
            case _:
                filtered_list = [
                    p
                    for p in dset_obj.out_of_file_avail_premises
                    if self.filter_premise(p)
                ]
                self.__oof_cache = OOFCache(dset_obj, filtered_list, set(filtered_list))
                return self.__oof_cache

    def get_oof_filtered_premises(self, dset_obj: DatasetFile) -> list[Sentence]:
        cache_result = self.__check_dset_cache(dset_obj)
        return cache_result.filtered_list

    def get_pos_filtered_premises(
        self,
        step: FocusedStep,
        proof: Proof,
        dset_obj: DatasetFile,
        oof_premises: set[Sentence],
        in_file_premises: set[Sentence],
    ) -> list[Sentence]:
        all_positive_candidates = step.step.context
        filtered_positive_candidates: list[Sentence] = []
        for pos_premise in all_positive_candidates:
            passes_filter = self.filter_premise(pos_premise)
            same_file = pos_premise.file_path == proof.theorem.term.file_path
            prev_line_in_file = same_file and (
                pos_premise.line < proof.theorem.term.line
            )
            premise_available = (not same_file) or prev_line_in_file
            premise_in_context = (pos_premise in in_file_premises) or (
                pos_premise in oof_premises
            )
            if passes_filter and premise_available and premise_in_context:
                filtered_positive_candidates.append(pos_premise)
            if passes_filter and not premise_available:
                _logger.warning(
                    f"Same file positive premise not available at {pos_premise.file_path}:{pos_premise.line}",
                )
            if passes_filter and not premise_in_context:
                _logger.warning(
                    f"Positive premise not in context at {pos_premise.file_path}:{pos_premise.line}",
                )

        return filtered_positive_candidates

    def get_pos_and_avail_premises(
        self, step: FocusedStep, proof: Proof, dset_obj: DatasetFile
    ) -> FilteredResult:
        """TODO: Change proof.line to step.line"""
        in_file_premises = self.get_in_file_filtered_premises(step, proof, dset_obj)
        cache_result = self.__check_dset_cache(dset_obj)
        filtered_avail_candidates = cache_result.filtered_list + in_file_premises
        filtered_pos_candidates = self.get_pos_filtered_premises(
            step, proof, dset_obj, cache_result.filtered_set, set(in_file_premises)
        )
        return FilteredResult(filtered_pos_candidates, filtered_avail_candidates)

    @classmethod
    def from_conf(cls, conf: PremiseFilterConf) -> PremiseFilter:
        coq_excludes: list[TermType] = []
        for exclude in conf.coq_excludes:
            coq_excludes.append(TermType[exclude])

        non_coq_excludes: list[TermType] = []
        for exclude in conf.non_coq_excludes:
            non_coq_excludes.append(TermType[exclude])

        general_excludes: list[TermType] = []
        for exclude in conf.general_excludes:
            general_excludes.append(TermType[exclude])

        return cls(coq_excludes, non_coq_excludes, general_excludes)


NO_COQ_LEMMA_FILTER = PremiseFilter(
    coq_excludes=[
        TermType.THEOREM,
        TermType.LEMMA,
        TermType.DEFINITION,
        TermType.NOTATION,
        TermType.INDUCTIVE,
        TermType.COINDUCTIVE,
        TermType.RECORD,
        TermType.CLASS,
        TermType.INSTANCE,
        TermType.FIXPOINT,
        TermType.COFIXPOINT,
        TermType.SCHEME,
        TermType.VARIANT,
        TermType.FACT,
        TermType.REMARK,
        TermType.COROLLARY,
        TermType.PROPOSITION,
        TermType.PROPERTY,
        TermType.OBLIGATION,
        TermType.TACTIC,
        TermType.RELATION,
        TermType.SETOID,
        TermType.FUNCTION,
        TermType.DERIVE,
        TermType.OTHER,
    ],
    non_coq_excludes=[
        TermType.DEFINITION,
        TermType.NOTATION,
        TermType.INDUCTIVE,
        TermType.COINDUCTIVE,
        TermType.RECORD,
        TermType.CLASS,
        TermType.INSTANCE,
        TermType.FIXPOINT,
        TermType.COFIXPOINT,
        TermType.SCHEME,
        TermType.VARIANT,
        TermType.OBLIGATION,
        TermType.TACTIC,
        TermType.RELATION,
        TermType.SETOID,
        TermType.FUNCTION,
        TermType.DERIVE,
        TermType.OTHER,
    ],
    general_excludes=[],
)
