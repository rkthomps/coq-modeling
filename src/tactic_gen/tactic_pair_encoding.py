from __future__ import annotations
from typing import Iterable, Optional, Any
import sys, os
import argparse
import heapq
import json
import csv

from tqdm import tqdm
from typeguard import typechecked

from data_management.dataset_file import DatasetFile, FocusedStep, data_shape_expected
from tactic_gen.step_parser import tokens2str, normalize, lex, get_id_strs

STEP_DELIM = " <++> "


@typechecked
class TacticPairEncoding:
    def __init__(self, vocab: dict[str, int]) -> None:
        assert type(vocab) == dict
        for k, v in vocab.items():
            assert type(k) == str
            assert type(v) == int
        self.vocab = vocab

    def contains(self, tac_list: list[str]) -> bool:
        return self.merge_steps(tac_list) in self.vocab

    def n_most_frequent_k_tac_seqs(self, n: int, k: int) -> list[tuple[str, int]]:
        tacs_of_k: list[tuple[int, str]] = []
        for tac, freq in self.vocab.items():
            exploded = self.__split_steps(tac)
            if len(exploded) == k:
                heapq.heappush(tacs_of_k, (freq, tac))
            if len(tacs_of_k) > n:
                heapq.heappop(tacs_of_k)
        return [(v2, v1) for v1, v2 in heapq.nlargest(n, tacs_of_k)]

    def get_report(self, n: int) -> list[tuple[int, list[tuple[str, int]]]]:
        cur_len = 1
        tacs_at_k = self.n_most_frequent_k_tac_seqs(n, cur_len)

        outer_list: list[tuple[int, list[tuple[str, int]]]] = []
        while len(tacs_at_k) > 0:
            inner_list: list[tuple[str, int]] = []
            for tac_str, freq in tacs_at_k:
                inner_list.append((tac_str, freq))
            outer_list.append((cur_len, inner_list))
            cur_len += 1
            tacs_at_k = self.n_most_frequent_k_tac_seqs(n, cur_len)
        return outer_list

    def print_report(self, n: int = 10) -> None:
        def format_num(n: int) -> str:
            return "{:5d}".format(n)

        for cur_len, tac_list in self.get_report(n):
            print(f"{n} Most Frequent Tactic Sequences of len {cur_len}:")
            for tac_str, tac_freq in tac_list:
                print(f"\t{format_num(tac_freq)} {tac_str}")
            print()

    def save_csv_reports(self, out_loc: str, n: int = 10) -> None:
        report_obj = self.get_report(n)
        if os.path.exists(out_loc):
            raise ValueError(f"{out_loc} exists.")
        with open(out_loc, "w") as fout:
            writer = csv.writer(fout)
            for k, tac_list in report_obj:
                writer.writerow([f"{k}-lists of Tactics", "Frequency", "Tactic List"])
                for tac_str, tac_freq in tac_list:
                    writer.writerow(["", tac_freq] + self.__split_steps(tac_str))
                writer.writerow([])

    def to_json(self) -> Any:
        return {"vocab": self.vocab}

    def save(self, path: str) -> None:
        if os.path.exists(path):
            raise ValueError(f"{path} exists.")
        with open(path, "w") as fout:
            fout.write(json.dumps(self.to_json(), indent=2))

    @classmethod
    def from_json(cls, json_data: Any) -> TacticPairEncoding:
        if "vocab" in json_data:
            vocab = json_data["vocab"]
            return cls(vocab)
        if "path" in json_data:
            return cls.load(json_data["path"])
        raise ValueError('Expected "vocab" or "path" in json data.')

    @classmethod
    def load(cls, path: str) -> TacticPairEncoding:
        with open(path, "r") as fin:
            json_data = json.load(fin)
            return cls.from_json(json_data)

    @classmethod
    def __merge_step_pair(cls, step1: str, step2: str) -> str:
        return cls.merge_steps([step1, step2])

    @staticmethod
    def merge_steps(step_list: list[str]) -> str:
        return STEP_DELIM.join(step_list)

    @staticmethod
    def __split_steps(steps: str) -> list[str]:
        return steps.split(STEP_DELIM)

    @staticmethod
    def __find_frequent_pair(
        step_lists: list[list[str]],
    ) -> Optional[tuple[tuple[str, str], int]]:
        pair_freqs: dict[tuple[str, str], int] = {}
        for step_list in step_lists:
            for i in range(len(step_list) - 1):
                pair = (step_list[i], step_list[i + 1])
                if pair not in pair_freqs:
                    pair_freqs[pair] = 0
                pair_freqs[pair] += 1

        if len(pair_freqs) == 0:
            return None
        max_pair = max(pair_freqs.items(), key=lambda item: item[1])
        return max_pair

    @classmethod
    def __update_step_lists(
        cls, step_lists: list[list[str]], pair: tuple[str, str]
    ) -> None:
        for step_list in step_lists:
            i = 0
            while i < len(step_list) - 1:
                if (step_list[i], step_list[i + 1]) == pair:
                    step_list.pop(i)
                    step_list.pop(i)
                    step_list.insert(i, cls.__merge_step_pair(*pair))
                i += 1

    @staticmethod
    def normalize_step(raw_step: str) -> str:
        return tokens2str(normalize(lex(raw_step)))

    @classmethod
    def create(cls, train_dataset_loc: str, n_merges: int) -> TacticPairEncoding:
        assert data_shape_expected(train_dataset_loc)
        step_lists: list[list[str]] = []
        for step_list in step_list_iterator(train_dataset_loc):
            try:
                str_step_list = [cls.normalize_step(s.step.text) for s in step_list]
                step_lists.append(str_step_list)
            except:
                continue

        step_vocab: dict[str, int] = {}
        for str_step_list in step_lists:
            for str_step in str_step_list:
                if str_step not in step_vocab:
                    step_vocab[str_step] = 0
                step_vocab[str_step] += 1
        print("Base Vocab Size:", len(step_vocab))

        for _ in tqdm(range(n_merges)):
            match cls.__find_frequent_pair(step_lists):
                case None:
                    print("got none")
                    break
                case (el1, el2), freq:
                    # print(cls.__merge_steps(el1, el2))
                    step_vocab[cls.__merge_step_pair(el1, el2)] = freq
                    cls.__update_step_lists(step_lists, (el1, el2))

        return cls(step_vocab)


def step_list_iterator(train_dataset_loc: str) -> Iterable[list[FocusedStep]]:
    assert data_shape_expected(train_dataset_loc)
    for dirname in os.listdir(train_dataset_loc):
        dir_loc = os.path.join(train_dataset_loc, dirname)
        dset_obj = DatasetFile.from_directory(dir_loc)
        for proof in dset_obj.proofs:
            yield proof.steps


def step_iterator(train_dataset_loc: str) -> Iterable[FocusedStep]:
    for step_list in step_list_iterator(train_dataset_loc):
        for step in step_list:
            yield step


def get_id_freq(train_dataset_loc: str) -> dict[str, int]:
    id_table: dict[str, int] = {}
    for step in step_iterator(train_dataset_loc):
        try:
            id_strs = get_id_strs(lex(step.step.text))
        except:
            continue
        for id_str in id_strs:
            if id_str not in id_table:
                id_table[id_str] = 0
            id_table[id_str] += 1
    return id_table


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "train_raw_data", help="Location of raw training data (the train partition)."
    )
    parser.add_argument("n_merges", type=int, help="Number of merges to use.")
    parser.add_argument("save_loc", help="Where to save the tactic pair encoding.")
    args = parser.parse_args(sys.argv[1:])
    tpe = TacticPairEncoding.create(args.train_raw_data, args.n_merges)
    tpe.print_report()
    tpe.save(args.save_loc)