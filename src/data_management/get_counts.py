from __future__ import annotations
from typing import Any, Optional

import sys, os
import enum
import argparse
import json
import re
import time
from multiprocessing import Pool, Manager
from queue import Queue

from typeguard import typechecked
from tqdm import tqdm

from coqpyt.coq.structs import TermType

from premise_selection.premise_filter import PremiseFilter
from data_management.dataset_file import DatasetFile, Sentence, data_shape_expected
from data_management.splits import DATA_POINTS_NAME


def remove_comments(step_text: str) -> str:
    new_step_text = step_text
    comment_match = re.search(r"\(\*.*?\*\)", new_step_text, re.DOTALL)
    while comment_match:
        new_step_text = new_step_text.replace(comment_match.group(), " ", 1)
        comment_match = re.search(r"\(\*.*?\*\)", new_step_text, re.DOTALL)
    return new_step_text


class Origin(enum.Enum):
    COQ_STD_LIB = 1
    COQ_USER_CONTRIB = 2
    LOCAL_IN_FILE = 3
    LOCAL_OUT_OF_FILE = 3


@typechecked
class PremTypeKey:
    def __init__(self, term_type: TermType, origin: Origin) -> None:
        assert type(term_type) == TermType
        assert type(origin) == Origin
        self.term_type = term_type
        self.origin = origin

    def __hash__(self) -> int:
        return hash((self.term_type, self.origin))

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, PremTypeKey):
            return False
        return hash(self) == hash(other)

    def to_json(self) -> Any:
        return {
            "term_type": self.term_type.name,
            "origin": self.origin.name,
        }

    def __repr__(self) -> str:
        return f"Origin: {self.origin.name}; Type: {self.term_type.name}."

    @classmethod
    def from_json(cls, json_data: Any) -> PremTypeKey:
        term_type = TermType[json_data["term_type"]]
        origin = Origin[json_data["origin"]]
        return cls(term_type, origin)


@typechecked
class PremTypeTable:
    def __init__(self, type_freqs: dict[PremTypeKey, int]) -> None:
        self.type_freqs = type_freqs

    def to_json(self) -> dict[str, dict[str, int]]:
        json_type_freqs: dict[str, int] = {}
        for k, v in self.type_freqs.items():
            str_key = json.dumps(k.to_json())
            json_type_freqs[str_key] = v
        return {"type_freqs": json_type_freqs}

    @classmethod
    def from_json(cls, json_data: dict[str, dict[str, int]]) -> PremTypeTable:
        type_freqs_dict = json_data["type_freqs"]
        assert type(type_freqs_dict) == dict
        type_freqs: dict[PremTypeKey, int] = {}
        for k, v in type_freqs_dict.items():
            obj_key = PremTypeKey.from_json(json.loads(k))
            type_freqs[obj_key] = v
        return cls(type_freqs)

    @staticmethod
    def get_origin(premise: Sentence, dset_file: DatasetFile) -> Origin:
        coq_lib_str = os.path.join("lib", "coq", "theories") + "/"
        if coq_lib_str in premise.file_path:
            return Origin.COQ_STD_LIB
        coq_contrib_str = os.path.join("lib", "user-contrib") + "/"
        if coq_contrib_str in premise.file_path:
            return Origin.COQ_USER_CONTRIB
        if premise.file_path == dset_file.file_context.file:
            return Origin.LOCAL_IN_FILE
        return Origin.LOCAL_OUT_OF_FILE

    @classmethod
    def from_premises(
        cls, premises: list[Sentence], dset_file: DatasetFile, weight: int = 1
    ) -> PremTypeTable:
        type_counts: dict[PremTypeKey, int] = {}
        for premise in premises:
            origin = cls.get_origin(premise, dset_file)
            term_type = premise.sentence_type
            premise_key = PremTypeKey(term_type, origin)
            if premise_key not in type_counts:
                type_counts[premise_key] = 0
            type_counts[premise_key] += weight
        return cls(type_counts)


@typechecked
class PremTableAggregator:
    def __init__(self, table_counts: PremTypeTable, num_tables: int) -> None:
        self.table_counts = table_counts
        self.num_tables = num_tables

    def add_table(self, table: PremTypeTable) -> None:
        for term_type, term_count in table.type_freqs.items():
            if term_type not in self.table_counts.type_freqs:
                self.table_counts.type_freqs[term_type] = 0
            self.table_counts.type_freqs[term_type] += term_count
        self.num_tables += 1

    def compute_by_key(self) -> dict[str, float]:
        return_table: dict[str, float] = {}
        for premise_key, count in self.table_counts.type_freqs.items():
            str_key = repr(premise_key)
            return_table[str_key] = count / self.num_tables
        return return_table

    def __repr__(self) -> str:
        return json.dumps(self.compute_by_key(), indent=2)

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
    def merge(
        cls, pta1: PremTableAggregator, pta2: PremTableAggregator
    ) -> PremTableAggregator:
        merged_table_counts: dict[PremTypeKey, int] = {}
        merged_num_tables = pta1.num_tables + pta2.num_tables
        for term_type, count in pta1.table_counts.type_freqs.items():
            if term_type not in merged_table_counts:
                merged_table_counts[term_type] = 0
            merged_table_counts[term_type] += count

        for term_type, count in pta2.table_counts.type_freqs.items():
            if term_type not in merged_table_counts:
                merged_table_counts[term_type] = 0
            merged_table_counts[term_type] += count
        merged_table = PremTypeTable(merged_table_counts)
        return cls(merged_table, merged_num_tables)

    @classmethod
    def get_empty(cls) -> PremTableAggregator:
        table_counts = PremTypeTable({})
        num_tables = 0
        return cls(table_counts, num_tables)


@typechecked
class PosPremiseAggregator(PremTableAggregator):
    def __init__(
        self,
        table_counts: PremTypeTable,
        num_tables: int,
        num_nonempty_premises: int,
        num_has_period: int,
    ) -> None:
        super(PosPremiseAggregator, self).__init__(table_counts, num_tables)
        self.num_nonempty_premises = num_nonempty_premises
        self.num_has_period = num_has_period

    def add_premise_step(self, step_text: str, pos_premises: list[Sentence], dset_file: DatasetFile) -> None:
        self.add_table(PremTypeTable.from_premises(pos_premises, dset_file))
        if len(pos_premises) > 0:
            self.num_nonempty_premises += 1
        step_without_comments = remove_comments(step_text)
        if "." in step_without_comments.strip().rstrip("."):
            print(step_text)
            self.num_has_period += 1

    def compute_by_key(self) -> dict[str, float]:
        return_table: dict[str, float] = {}
        for key, count in self.table_counts.type_freqs.items():
            str_key = repr(key)
            return_table[str_key] = count / self.num_nonempty_premises
        return return_table

    def __repr__(self) -> str:
        step_needs_premise_freq = self.num_nonempty_premises / self.num_tables
        w_pos_prem_and_period = self.num_has_period / self.num_nonempty_premises
        strs: list[str] = [
            f"Step Needs Premise Freq: {step_needs_premise_freq}",
            f"Steps w/ pos prem & period: {w_pos_prem_and_period}",
            f"Steps w/ pos prem term type freqs:\n{json.dumps(self.compute_by_key(), indent=2)}",
        ]
        return "\n".join(strs)

    def to_json(self) -> Any:
        parent_json_dict = super(PosPremiseAggregator, self).to_json()
        parent_json_dict["num_nonempty_premises"] = self.num_nonempty_premises
        parent_json_dict["num_has_period"] = self.num_has_period
        return parent_json_dict

    @classmethod
    def from_json(cls, json_data: Any) -> PosPremiseAggregator:
        parent_aggregator = PremTableAggregator.from_json(json_data)
        num_nonempty_premises = json_data["num_nonempty_premises"]
        num_has_period = json_data["num_has_period"]
        return cls(
            parent_aggregator.table_counts,
            parent_aggregator.num_tables,
            num_nonempty_premises,
            num_has_period,
        )

    @classmethod
    def merge_pos(
        cls, ppa1: PosPremiseAggregator, ppa2: PosPremiseAggregator
    ) -> PosPremiseAggregator:
        merged_parent = PremTableAggregator.merge(ppa1, ppa2)
        merged_nonempty_prems = ppa1.num_nonempty_premises + ppa2.num_nonempty_premises
        merged_has_period = ppa1.num_has_period + ppa2.num_has_period
        return cls(
            merged_parent.table_counts,
            merged_parent.num_tables,
            merged_nonempty_prems,
            merged_has_period,
        )

    @classmethod
    def get_empty(cls) -> PosPremiseAggregator:
        table_counts = PremTypeTable({})
        num_tables = 0
        nonempty_prems = 0
        has_period = 0
        return cls(table_counts, num_tables, nonempty_prems, has_period)


class FileResult:
    def __init__(
        self,
        num_proofs: int,
        num_steps: int,
        num_files: int,
        avail_aggregator: PremTableAggregator,
        pos_aggregator: PosPremiseAggregator,
    ) -> None:
        self.num_proofs = num_proofs
        self.num_steps = num_steps
        self.num_files = num_files
        self.avail_aggregator = avail_aggregator
        self.pos_aggregator = pos_aggregator

    @classmethod
    def merge(cls, fr1: FileResult, fr2: FileResult) -> FileResult:
        num_proofs = fr1.num_proofs + fr2.num_proofs
        num_steps = fr1.num_steps + fr2.num_steps
        num_files = fr1.num_files + fr2.num_files
        merged_avail = PremTableAggregator.merge(
            fr1.avail_aggregator, fr2.avail_aggregator
        )
        merged_pos = PosPremiseAggregator.merge_pos(
            fr1.pos_aggregator, fr2.pos_aggregator
        )
        return cls(num_proofs, num_steps, num_files, merged_avail, merged_pos)

    def to_json(self) -> Any:
        return {
            "num_proofs": self.num_proofs,
            "num_steps": self.num_steps,
            "num_files": self.num_files,
            "avail_aggregator": self.avail_aggregator.to_json(),
            "pos_aggregator": self.pos_aggregator.to_json(),
        }

    def save(self, file_path: str) -> None:
        json_rep = self.to_json()
        with open(file_path, "w") as fout:
            fout.write(json.dumps(json_rep, indent=2))

    @classmethod
    def load(cls, file_path: str) -> FileResult:
        with open(file_path, "r") as fin:
            file_result_data = json.load(fin)
        return cls.from_json(file_result_data)

    @classmethod
    def from_json(cls, json_data: Any) -> FileResult:
        num_proofs = json_data["num_proofs"]
        num_steps = json_data["num_steps"]
        num_files = json_data["num_files"]
        avail_aggregator_data = json_data["avail_aggregator"]
        avail_aggregator = PremTableAggregator.from_json(avail_aggregator_data)
        pos_aggregator_data = json_data["pos_aggregator"]
        pos_aggregator = PosPremiseAggregator.from_json(pos_aggregator_data)
        return cls(num_proofs, num_steps, num_files, avail_aggregator, pos_aggregator)

    @classmethod
    def from_file(cls, dset_file: DatasetFile) -> FileResult:
        premise_filter = PremiseFilter()
        avail_aggregator = PremTableAggregator.get_empty()
        pos_aggregator = PosPremiseAggregator.get_empty()
        num_steps = 0
        oof_premises = premise_filter.get_oof_filtered_premises(dset_file)
        oof_set = set(oof_premises)
        for proof in dset_file.proofs:
            for step in proof.steps:
                in_file_premises = premise_filter.get_in_file_filtered_premises(
                    step, proof, dset_file
                )
                pos_premises = premise_filter.get_pos_filtered_premises(
                    step, proof, dset_file, oof_set, set(in_file_premises)
                )
                pos_aggregator.add_premise_step(step.step.text, pos_premises, dset_file)
                in_file_avail_table = PremTypeTable.from_premises(in_file_premises, dset_file)
                avail_aggregator.add_table(in_file_avail_table)
            num_steps += len(proof.steps)
        num_proofs = len(dset_file.proofs)
        num_files = 1
        oof_avail_table = PremTypeTable.from_premises(oof_premises, dset_file, weight=num_steps)
        avail_aggregator.add_table(oof_avail_table)
        return cls(num_proofs, num_steps, num_files, avail_aggregator, pos_aggregator)

    @classmethod
    def get_empty(cls) -> FileResult:
        num_proofs = 0
        num_steps = 0
        num_files = 0
        avail_aggregator = PremTableAggregator.get_empty()
        pos_aggregator = PosPremiseAggregator.get_empty()
        return cls(num_proofs, num_steps, num_files, avail_aggregator, pos_aggregator)


def counter(total: int, q: Queue[Optional[int]]) -> None:
    tally = 0
    while True:
        i = q.get()
        if i is None:
            return
        tally += i
        print(f"\r{tally} of {total} files analized.", end="")


def get_file_aggregator(file_dirname: str, q: Queue[Optional[int]]) -> FileResult:
    dset_file = DatasetFile.from_directory(file_dirname)
    q.put(1)
    return FileResult.from_file(dset_file)


def get_arguments(
    raw_dataset_loc: str, q: Queue[Optional[int]]
) -> list[tuple[str, Queue[Optional[int]]]]:
    args: list[tuple[str, Queue[Optional[int]]]] = []
    assert data_shape_expected(raw_dataset_loc)
    for coq_file_dir in os.listdir(raw_dataset_loc):
        coq_file_dir_loc = os.path.join(raw_dataset_loc, coq_file_dir)
        args.append((coq_file_dir_loc, q))
    return args


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "dataset_loc",
        type=str,
        help="Location of raw data with datapoints and repos underneith.",
    )
    parser.add_argument("out_loc", help="Where to put the resulting json file.")
    parser.add_argument(
        "--num_procs", "-n", type=int, help="Number of cores to use to calc result"
    )
    args = parser.parse_args(sys.argv[1:])
    if os.path.exists(args.out_loc):
        raise ValueError(f"{args.out_loc} exists.")

    n_procs = 1
    if args.num_procs is not None:
        n_procs = args.num_procs
    data_points_loc = os.path.join(args.dataset_loc, DATA_POINTS_NAME)

    print("Processing")
    with Manager() as manager:
        q = manager.Queue()
        with Pool(n_procs) as pool:
            arguments = get_arguments(data_points_loc, q)
            async_counter = pool.apply_async(counter, (len(arguments), q))
            results = pool.starmap(get_file_aggregator, arguments)
            q.put(None)
            async_counter.wait()

    print("Aggregating...")
    cur_file_aggregator = FileResult.get_empty()
    for result in results:
        cur_file_aggregator = FileResult.merge(cur_file_aggregator, result)

    cur_file_aggregator.save(args.out_loc)
