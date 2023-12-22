
from typing import Any, Optional

import sys, os
import yaml
import argparse

from transformers import Trainer  

from proof_selection.proof_selection_model import ProofSelector
from util.train_utils import get_training_args

def get_trainer(conf: Any, local_rank: Optional[int]) -> Trainer:
    model = ProofSelector()
    trainer = Trainer()

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Train a proof retrieval model.")
    parser.add_argument(
        "--local_rank",
        type=int,
        default=-1,
        help="local rank passed from distributed launcher",
    )
    parser.add_argument(
        "training_conf", help="Location of training configuration file."
    )
    args = parser.parse_args(sys.argv[1:])

    with open(args.trianing_conf, "r") as fin:
        conf = yaml.load(fin, Loader=yaml.Loader)
