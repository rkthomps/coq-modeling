from __future__ import annotations
from typing import Any

import sys, os
import argparse
import json
import re

from tqdm import tqdm

from coqlspclient.coq_structs import TermType

from premise_selection.premise_filter import PremiseFilter
from data_management.dataset_file import DatasetFile, Sentence, data_shape_expected
from data_management.split_raw_data import SPLITS 



class PremTypeTable:
    def __init__(self, type_freqs: dict[TermType, int]) -> None:
        assert type(type_freqs) == dict 
        assert all([(type(k) == TermType and type(v) == int) for k, v in type_freqs.items()])
        self.type_freqs = type_freqs

    def to_json(self) -> Any:
        return {"type_freqs": dict((t.name, v) for t, v in self.type_freqs.items())}

    @classmethod
    def from_premises(cls, premises: list[Sentence]) -> PremTypeTable:
        type_counts: dict[TermType, int] = {}
        for premise in premises:
            if premise.sentence_type not in type_counts:
                type_counts[premise.sentence_type] = 0
            type_counts[premise.sentence_type] += 1
        return cls(type_counts)

    @classmethod
    def from_json(cls, json_data: Any) -> PremTypeTable:
        type_freqs_dict = json_data["type_freqs"]
        assert type(type_freqs_dict) == dict
        type_freqs = dict((TermType[k], v) for k, v in type_freqs_dict.items())
        return cls(type_freqs)


class PremTableAggregator:
    def __init__(self, table_counts: PremTypeTable, num_tables: int) -> None:
        assert type(table_counts) == PremTypeTable
        assert type(num_tables) == int
        self.table_counts = table_counts 
        self.num_tables = num_tables 

    def add_table(self, table: PremTypeTable) -> None:
        for term_type, term_count in table.type_freqs.items():
            if term_type not in self.table_counts.type_freqs:
                self.table_counts.type_freqs[term_type] = 0
            self.table_counts.type_freqs[term_type] += term_count
        self.num_tables += 1

    def compute(self) -> dict[str, float]:
        return_table: dict[str, float] = {} 
        for term_type, term_count in self.table_counts.type_freqs.items():
            return_table[term_type.name] = term_count / self.num_tables
        return return_table

    def __repr__(self) -> str:
        return json.dumps(self.compute(), indent=2)

    def to_json(self) -> Any:
        return {
            "table_counts": self.table_counts.to_json(),
            "num_tables": self.num_tables,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> PremTableAggregator:
        table_counts_data = json_data["table_counts"] 
        table_counts = PremTypeTable.from_json(table_counts_data)
        num_tables = json_data["num_tables"]
        return cls(table_counts, num_tables)

    @classmethod
    def get_empty(cls) -> PremTableAggregator:
        table_counts = PremTypeTable({})
        num_tables = 0
        return cls(table_counts, num_tables)


class PosPremiseAggregator(PremTableAggregator):
    def __init__(self, table_counts: PremTypeTable, num_tables: int,
                 num_nonempty_premises: int, num_has_period: int) -> None:
        super(PosPremiseAggregator, self).__init__(table_counts, num_tables)
        self.num_nonempty_premises = num_nonempty_premises
        self.num_has_period = num_has_period 

    def __remove_comments(self, step_text: str) -> str:
        new_step_text = step_text
        comment_match = re.search(r"\(\*.*?\*\)", new_step_text, re.DOTALL)
        while comment_match:
            new_step_text = new_step_text.replace(comment_match.group(), " ", 1)
            comment_match = re.search(r"\(\*.*?\*\)", new_step_text, re.DOTALL)
        return new_step_text 


    def add_premise_step(self, step_text: str, pos_premises: list[Sentence]) -> None:
        self.add_table(PremTypeTable.from_premises(pos_premises))
        if len(pos_premises) > 0:
            self.num_nonempty_premises += 1
        step_without_comments = self.__remove_comments(step_text)
        if "." in step_without_comments.strip().rstrip("."):
            print(step_text)
            self.num_has_period += 1


    def compute(self) -> dict[str, float]:
        return_table: dict[str, float] = {}
        for term_type, term_count in self.table_counts.type_freqs.items():
            return_table[term_type.name] = term_count / self.num_nonempty_premises 
        return return_table


    def __repr__(self) -> str:
        step_needs_premise_freq = self.num_nonempty_premises / self.num_tables
        w_pos_prem_and_period = self.num_has_period / self.num_nonempty_premises
        strs: list[str] = [
            f"Step Needs Premise Freq: {step_needs_premise_freq}",
            f"Steps w/ pos prem & period: {w_pos_prem_and_period}",
            f"Steps w/ pos prem term type freqs:\n{json.dumps(self.compute(), indent=2)}"
        ]
        return "\n".join(strs)


    def to_json(self) -> Any:
        parent_json_dict = super().to_json()
        parent_json_dict["num_nonempty_premises"] = self.num_nonempty_premises
        parent_json_dict["num_has_period"] = self.num_has_period


    @classmethod
    def from_json(cls, json_data: Any) -> PosPremiseAggregator: 
        parent_aggregator = PremTableAggregator.from_json(json_data)
        num_nonempty_premises = json_data["num_nonempty_premises"]
        num_has_period = json_data["num_has_period"]
        return cls(
            parent_aggregator.table_counts,
            parent_aggregator.num_tables,
            num_nonempty_premises, 
            num_has_period)


class FileResult:
    def __init__(self, num_proofs: int, num_steps: int, num_files: int,
                 avail_aggregator: PremTableAggregator,
                 pos_aggregator: PosPremiseAggregator) -> None:
        self.num_proofs = num_proofs
        self.num_steps = num_steps
        self.num_files = num_files
        self.avail_aggregator = avail_aggregator
        self.pos_aggregator = pos_aggregator




def get_counts(partitioned_dataset_loc: str) -> None:
    num_proofs = 0
    num_steps = 0
    pos_premise_aggregator = PosPremiseAggregator() 
    avail_premise_aggregator = PremTableAggregator()

    premise_filter = PremiseFilter()

#    for split in SPLITS:
    for split in ["val"]:
        split_loc = os.path.join(partitioned_dataset_loc, split)
        assert data_shape_expected(split_loc) 
        print(f"Getting Counts for {split}...")
        for coq_file_dir in tqdm(os.listdir(split_loc)[:10]):
            coq_file_dir_loc = os.path.join(split_loc, coq_file_dir)
            dset_file = DatasetFile.from_directory(coq_file_dir_loc) 
            for proof in dset_file.proofs:
                num_proofs += 1
                for step in proof.steps:
                    filter_result = premise_filter.get_pos_and_avail_premises(
                        step, proof, dset_file)
                    pos_premise_aggregator.add_premise_step(step.step.text, filter_result.pos_premises)
                    avail_table = PremTypeTable.from_premises(filter_result.avail_premises)
                    avail_premise_aggregator.add_table(avail_table)
                    num_steps += 1

    print(f"Num Proofs: {num_proofs}")
    print(f"Num Steps: {num_steps}")
    print(f"Avail Premises: \n{repr(avail_premise_aggregator)}")
    print(f"Positive Premises: \n{repr(pos_premise_aggregator)}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("partitioned_dataset_loc", type=str,
                        help="Location of partitioned raw data.")
    args = parser.parse_args(sys.argv[1:])
    get_counts(args.partitioned_dataset_loc)