from __future__ import annotations
import sys, os
import argparse
import re
from data_management.dataset_file import DatasetFile, data_shape_expected


class TacticPatterns:
    __ws = r"\s*"
    __def_ws = r"\s+"
    __id_chars = r"[a-zA-Z0-9_]+"
    __arg = __def_ws + f"({__id_chars})"
    __args = f"{__arg}*{__ws}\\."
    INTROS = re.compile(f"{__ws}intros{__args}")

    PATTERNS = [INTROS]


class TacticPattern:
    def __init__(self, pattern: str) -> None:
        self.pattern = pattern


class TacticPairEncoding:
    def __init__(self) -> None:
        pass

    @classmethod
    def create(cls, train_dataset_loc: str, n_merges: int) -> TacticPairEncoding:
        assert data_shape_expected(train_dataset_loc)
        for dirname in os.listdir(train_dataset_loc):
            dir_loc = os.path.join(train_dataset_loc, dirname)
            dset_obj = DatasetFile.from_directory(dir_loc)
            for proof in dset_obj.proofs:
                for step in proof.steps:
                    matched = False
                    for pattern in TacticPatterns.PATTERNS:
                        match = pattern.match(step.step.text)
                        if match:
                            print("MATCHED:", match.groups())
                            matched = True
                            break
                    if not matched:
                        print("NOT MATCHED:", step.step.text)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "train_raw_data", help="Location of raw training data (the train partition)."
    )
    args = parser.parse_args(sys.argv[1:])
    TacticPairEncoding.create(args.train_raw_data, 10)
