

import sys, os
import argparse

from tqdm import tqdm

from data_management.dataset_file import DatasetFile 
from data_management.split_raw_data import SPLITS, data_shape_expected


def get_counts(partitioned_dataset_loc: str) -> None:
    num_proofs = 0
    num_steps = 0
    for split in SPLITS:
        split_loc = os.path.join(partitioned_dataset_loc, split)
        assert data_shape_expected(split_loc) 
        print(f"Getting Counts for {split}...")
        for coq_file_dir in tqdm(os.listdir(split_loc)):
            coq_file_dir_loc = os.path.join(split_loc, coq_file_dir)
            dset_file = DatasetFile.from_directory(coq_file_dir_loc) 
            for proof in dset_file.proofs:
                num_proofs += 1
                for step in proof.steps:
                    num_steps += 1
    print(f"Num Proofs: {num_proofs}")
    print(f"Num Steps: {num_steps}")
        


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("partitioned_dataset_loc", type=str,
                        help="Location of partitioned raw data.")
    args = parser.parse_args(sys.argv[1:])
    get_counts(args.partitioned_dataset_loc)