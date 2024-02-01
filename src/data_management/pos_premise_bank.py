from __future__ import annotations

from typing import Any
import os
import sys
import multiprocessing as mp
import argparse
import json
from queue import Queue


from data_management.dataset_file import Sentence
from data_management.splits import DataSplit, Split, FileInfo


class PosPremiseBank:
    def __init__(self, premises: set[Sentence]) -> None:
        self.premises = premises

    def contains(self, premise: Sentence) -> bool:
        return premise in self.premises

    def add(self, premise: Sentence) -> None:
        self.premises.add(premise)

    def merge(self, other: PosPremiseBank) -> None:
        self.premises |= other.premises

    def to_json(self) -> Any:
        return {"premises": [p.to_json() for p in self.premises]}

    def save(self, file_loc: str) -> None:
        file_dirname = os.path.dirname(file_loc)
        os.makedirs(file_dirname, exist_ok=True)
        with open(file_loc, "w") as fout:
            fout.write(json.dumps(self.to_json(), indent=2))

    @classmethod
    def load(cls, path: str) -> PosPremiseBank:
        with open(path, "r") as fin:
            json_data = json.load(fin)
            return cls.from_json(json_data)

    @classmethod
    def empty(cls) -> PosPremiseBank:
        return cls(set())

    @classmethod
    def from_json(cls, json_data: Any) -> PosPremiseBank:
        premises = set([Sentence.from_json(p) for p in json_data["premises"]])
        return cls(premises)


_ARG = tuple[str, FileInfo, Queue[bool]]


def get_pos_bank(data_loc: str, file_info: FileInfo, q: Queue[bool]) -> PosPremiseBank:
    try:
        proofs = file_info.get_proofs(data_loc)
    except FileNotFoundError:
        return PosPremiseBank.empty()
    pos_bank = PosPremiseBank.empty()
    for proof in proofs:
        for step in proof.steps:
            for premise in step.step.context:
                pos_bank.add(premise)
    q.put(True)
    return pos_bank


def writer(q: Queue[bool]) -> None:
    num_examples_written = 0
    while True:
        example = q.get()
        if example:
            num_examples_written += 1
            print(f"\rNum Files: {num_examples_written}", end="")
        else:
            print()
            return


def get_bank_args(data_loc: str, data_split: DataSplit, q: Queue[bool]) -> list[_ARG]:
    args: list[_ARG] = []
    for file_info in data_split.get_file_list(data_loc, Split.TRAIN)[:1000]:
        args.append((data_loc, file_info, q))
    return args


if __name__ == "__main__":
    parser = argparse.ArgumentParser("Create positive premise bank.")
    parser.add_argument("--n_procs", "-n", type=int, help="Number of processes.")
    parser.add_argument("data_loc", help="Location of raw data")
    parser.add_argument("data_split_loc", help="Location of data split to use.")
    parser.add_argument("save_loc", help="Where to save the positive premise bank.")
    args = parser.parse_args(sys.argv[1:])

    n_procs = 1
    if args.n_procs:
        n_procs = args.n_procs
    data_split = DataSplit.load(args.data_split_loc)

    with mp.Manager() as manager:
        q: Queue[bool] = manager.Queue()
        arg_list = get_bank_args(args.data_loc, data_split, q)
        with mp.Pool(n_procs) as pool:
            reporter = pool.apply_async(writer, (q,))
            banks = pool.starmap(get_pos_bank, arg_list)
            q.put(False)
            reporter.wait()

    print("Aggregating")
    total_bank = PosPremiseBank.empty()
    for bank in banks:
        total_bank.merge(bank)
    total_bank.save(args.save_loc)
