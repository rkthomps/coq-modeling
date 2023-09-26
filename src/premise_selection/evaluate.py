
import sys, os
import argparse

from data_management.split_raw_data import SPLITS
from data_management.split_raw_data import data_shape_expected
from data_management.dataset_file import DatasetFile

from premise_selection.model import PremiseRetriever 


def load_model(model_loc: str) -> PremiseRetriever:
    pass


def evaluate(model_loc: str, 
             partitiond_data_loc: str,
             split: str) -> None:
    assert type(model_loc) == str
    assert type(partitiond_data_loc) == str
    assert type(split) == str
    assert split in SPLITS
    split_loc = os.path.join(partitiond_data_loc, split)
    assert data_shape_expected(split_loc)
    for raw_dataset_file in os.listdir(split_loc):
        parsed_dataset_file = DatasetFile.from_directory(raw_dataset_file)

        



if __name__=="__main__":
    parser = argparse.ArgumentParser(
        description="Conduct an evaluation of a premise selection model.")
    parser.add_argument("model_loc",
                        help="Location of the model to evaluate.")
    parser.add_argument("partitioned_data_loc",
                        help="Location of partitioned raw data to evaluate.")
    parser.add_argument("split",
                        help=f"Partition of data to evaluate. One of {SPLITS}")
    args = parser.parse_args(sys.argv[1:])

            
                    