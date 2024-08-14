from typing import Any
import sys, os
import argparse
from pathlib import Path
import random
import yaml


from tactic_gen.tactic_data import LmProcessedDataset, example_collator_from_conf
from tactic_gen.train_decoder import get_tokenizer, get_datasets

from util.train_utils import get_required_arg


def print_examples(training_conf: Any, num_examples: int):
    tokenizer = get_tokenizer(training_conf)
    train_dset, val_dset = get_datasets(training_conf, tokenizer)
    random.seed(0)
    example_idxs = random.sample(range(len(train_dset)), num_examples)
    for idx in example_idxs:
        example = train_dset[idx]
        print(tokenizer.decode(example["input_ids"]))
        print("\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("train_conf_loc")
    parser.add_argument("num_examples", type=int)
    args = parser.parse_args(sys.argv[1:])
    train_conf_loc = Path(args.train_conf_loc)

    with train_conf_loc.open("r") as fin:
        conf = yaml.load(fin, Loader=yaml.Loader)

    print_examples(conf, args.num_examples)
