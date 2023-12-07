from typing import Generator

import sys, os
import argparse
import random
import dataclasses

from tqdm import tqdm

from tactic_gen.proof_distance import norm_levenshtein_dist
from data_management.dataset_file import DatasetFile, Proof


@dataclasses.dataclass
class IntRange:
    start: int
    end: int

    def __hash__(self) -> int:
        return hash((self.start, self.end))

    def contains(self, val: int) -> bool:
        return self.start <= val <= self.end


@dataclasses.dataclass
class FloatRange:
    start: float
    end: float

    def __hash__(self) -> int:
        return hash((self.start, self.end))

    def contains(self, val: float) -> bool:
        return self.start <= val <= self.end


SpaceDict = dict[tuple[IntRange, FloatRange], list[tuple[Proof, Proof]]]


def __init_spaces(
    length_ranges: list[IntRange], score_ranges: list[FloatRange]
) -> SpaceDict:
    space_dict: SpaceDict = {}
    for lrange in length_ranges:
        for srange in score_ranges:
            space_dict[(lrange, srange)] = []
    return space_dict


def __spaces_complete(spaces: SpaceDict, n_per_space: int) -> bool:
    for _, v in spaces.items():
        if len(v) < n_per_space:
            return False
    return True


def __spaces_insert(spaces: SpaceDict, proof1: Proof, proof2: Proof) -> None:
    proof1_length = len(proof1.steps)
    proof2_length = len(proof2.steps)
    dist = norm_levenshtein_dist(proof1, proof2)
    spaces_keys = spaces.keys()
    for lrange, srange in spaces_keys:
        if (
            lrange.contains(proof1_length) or lrange.contains(proof2_length)
        ) and srange.contains(dist):
            spaces[(lrange, srange)].append((proof1, proof2))


def __show_spaces(spaces: SpaceDict, n_examples: int) -> None:
    for (lrange, srange), proofs in spaces.items():
        print("=" * 40)
        print(
            f"Proofs of length [{lrange.start}, {lrange.end}]; Scores in [{srange.start}, {srange.end}]"
        )
        print(f"Showing {n_examples} of {len(proofs)}")
        print("=" * 40)
        for proof1, proof2 in proofs[:n_examples]:
            print("-" * 40)
            print("Score:", norm_levenshtein_dist(proof1, proof2))
            print("Proof1:")
            print(proof1.proof_text_to_string())
            print("Proof2:")
            print(proof2.proof_text_to_string())
            print("-" * 40)


def __get_dp_obj(dp_path: str, dp_cache: dict[str, DatasetFile]) -> DatasetFile:
    if dp_path in dp_cache:
        return dp_cache[dp_path]
    dp_file = DatasetFile.from_directory(dp_path)
    dp_cache[dp_path] = dp_file
    return dp_file


def proof_pair_gen(data_points_loc: str) -> Generator[tuple[Proof, Proof], None, None]:
    data_points_names = random.sample(os.listdir(data_points_loc), 50)
    data_points_files = [os.path.join(data_points_loc, n) for n in data_points_names]
    print("Loading datapoints objs...")
    dp_objs = [DatasetFile.from_directory(dp_loc) for dp_loc in tqdm(data_points_files)]
    proof_pairs: list[tuple[Proof, Proof]] = []
    print("Gathering Proof Pairs...")
    for i in tqdm(range(len(dp_objs))):
        for j in range(i + 1, len(dp_objs)):
            dp1 = dp_objs[i]
            dp2 = dp_objs[j]
            for proof1 in dp1.proofs:
                for proof2 in dp2.proofs:
                    proof_pairs.append((proof1, proof2))
    random.shuffle(proof_pairs)
    for pp in proof_pairs:
        yield pp


def get_examples(
    data_points_loc: str,
    length_ranges: list[IntRange],
    score_ranges: list[FloatRange],
    n_per_space: int,
) -> None:
    random.seed(1)
    spaces = __init_spaces(length_ranges, score_ranges)
    for p1, p2 in proof_pair_gen(data_points_loc):
        __spaces_insert(spaces, p1, p2)
        if __spaces_complete(spaces, n_per_space):
            __show_spaces(spaces, n_per_space)
            return
    __show_spaces(spaces, n_per_space)


if __name__ == "__main__":
    sys.setrecursionlimit(1500)
    parser = argparse.ArgumentParser(
        "Find examples with varying levenshtein distances."
    )
    parser.add_argument(
        "data_points_loc", help="Directory containing data points files."
    )
    args = parser.parse_args(sys.argv[1:])

    l_ranges = [
        IntRange(0, 10),
        IntRange(10, 20),
    ]

    s_ranges = [
        FloatRange(0.0, 0.099),
        FloatRange(0.1, 0.199),
        FloatRange(0.2, 0.299),
        FloatRange(0.3, 0.399),
        FloatRange(0.4, 0.499),
        FloatRange(0.5, 0.599),
        FloatRange(0.6, 0.699),
        FloatRange(0.7, 0.799),
        FloatRange(0.8, 0.899),
        FloatRange(0.9, 1),
    ]

    examples_per_space = 5

    get_examples(args.data_points_loc, l_ranges, s_ranges, examples_per_space)
