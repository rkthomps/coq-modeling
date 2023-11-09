from __future__ import annotations
from typing import Any

import sys, os

from data_management.dataset_file import DatasetFile, Proof, FocusedStep, Sentence
from coqpyt.coq.structs import TermType


class FilteredResult:
    def __init__(
        self, pos_premises: list[Sentence], avail_premises: list[Sentence]
    ) -> None:
        assert type(pos_premises) == list
        assert all([type(p) == Sentence for p in pos_premises])
        assert all([type(p) == Sentence for p in avail_premises])
        self.pos_premises = pos_premises
        self.avail_premises = avail_premises


class PremiseFilter:
    def __init__(
        self,
        coq_excludes: list[TermType] = [],
        non_coq_excludes: list[TermType] = [],
        general_excludes: list[TermType] = [],
    ) -> None:
        assert type(coq_excludes) == list
        assert type(non_coq_excludes) == list
        assert type(general_excludes) == list
        assert all([type(t) == TermType for t in coq_excludes])
        assert all([type(t) == TermType for t in non_coq_excludes])
        assert all([type(t) == TermType for t in general_excludes])
        self.coq_excludes = coq_excludes
        self.non_coq_excludes = non_coq_excludes
        self.general_excludes = general_excludes
        self.__print_warnings()

    def __print_warnings(self) -> None:
        if len(self.coq_excludes) > 0:
            print(
                (
                    f"Excluding term types {self.coq_excludes} for premise selection "
                    "if they come from the coq standard library."
                )
            )
        if len(self.non_coq_excludes) > 0:
            print(
                f"Excluding term types {self.non_coq_excludes} for premise selection "
                "if they do not come from the coq standard library."
            )
        if len(self.general_excludes) > 0:
            print(
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

    def get_pos_and_avail_premises(
        self, step: FocusedStep, proof: Proof, dset_obj: DatasetFile
    ) -> FilteredResult:
        """TODO: Change proof.line to step.line"""
        all_premise_candidates = dset_obj.get_premises_before(proof)
        filtered_premise_candidates: list[Sentence] = []
        for premise in all_premise_candidates:
            if self.filter_premise(premise):
                filtered_premise_candidates.append(premise)

        all_positive_candidates = step.step.context
        filtered_positive_candidates: list[Sentence] = []
        for pos_premise in all_positive_candidates:
            passes_filter = self.filter_premise(pos_premise)
            same_file = pos_premise.file_path == proof.theorem.term.file_path
            prev_line_in_file = same_file and (
                pos_premise.line < proof.theorem.term.line
            )
            premise_available = (not same_file) or prev_line_in_file
            premise_in_context = pos_premise in all_premise_candidates
            if passes_filter and premise_available and premise_in_context:
                filtered_positive_candidates.append(pos_premise)
            if not premise_available:
                print(
                    f"Same file positive premise not available at {pos_premise.file_path}:{pos_premise.line}",
                    file=sys.stderr,
                )
            if not premise_in_context:
                print(
                    f"Positive premise not in context at {pos_premise.file_path}:{pos_premise.line}",
                    file=sys.stderr,
                )
        return FilteredResult(filtered_positive_candidates, filtered_premise_candidates)

    def to_json(self) -> Any:
        return {
            "coq_excludes": [t.name for t in self.coq_excludes],
            "non_coq_excludes": [t.name for t in self.non_coq_excludes],
            "general_excludes": [t.name for t in self.general_excludes],
        }

    @classmethod
    def from_json(cls, conf: Any) -> PremiseFilter:
        coq_exclude_data = conf["coq_excludes"]
        coq_excludes: list[TermType] = []
        for exclude in coq_exclude_data:
            coq_excludes.append(TermType[exclude])

        non_coq_exclude_data = conf["non_coq_excludes"]
        non_coq_excludes: list[TermType] = []
        for exclude in non_coq_exclude_data:
            non_coq_excludes.append(TermType[exclude])

        general_exclude_data = conf["general_excludes"]
        general_excludes: list[TermType] = []
        for exclude in general_exclude_data:
            general_excludes.append(TermType[exclude])

        return cls(coq_excludes, non_coq_excludes, general_excludes)
