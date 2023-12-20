from __future__ import annotations
from dataclasses import dataclass
from typing import Optional, Any
import sys, os
import shutil

import argparse
from queue import Queue
import multiprocessing as mp
import json

import yaml

from data_management.splits import DataSplit, FileInfo, Split, split_file_path
from data_management.jsonl_utils import deduplicate, shuffle
from tactic_gen.step_parser import lex, tokens2str, normalize, CoqParseError
from proof_selection.proof_selection_example import (
    context_formatter_from_conf,
    candidate_formatter_from_conf,
    ContextFormatter,
    CandidateFormatter,
    ProofSelectionExample,
)

PROOF_CONF_NAME = "proof_conf.yaml"


@dataclass
class ProofSelectionConfig:
    context_formatter: ContextFormatter
    candidate_formatter: CandidateFormatter
    data_loc: str
    out_loc: str
    data_split: DataSplit

    @classmethod
    def from_conf(cls, conf: Any) -> ProofSelectionConfig:
        context_formatter = context_formatter_from_conf(conf["context_formatter"])
        candidate_formatter = candidate_formatter_from_conf(conf["candidate_formatter"])
        data_loc = conf["data_loc"]
        out_loc = conf["out_loc"]
        data_split = DataSplit.load(conf["data_split_loc"])
        return cls(
            context_formatter, candidate_formatter, data_loc, out_loc, data_split
        )

    @classmethod
    def load(cls, path: str) -> ProofSelectionConfig:
        with open(path, "r") as fin:
            conf = yaml.load(fin, Loader=yaml.Loader)
        return cls.from_conf(conf)


def examples_to_queue(
    config: ProofSelectionConfig,
    file_info: FileInfo,
    q: Queue[Optional[ProofSelectionExample]],
) -> None:
    dp_obj = file_info.get_dp(config.data_loc)
    for proof in dp_obj.proofs:
        try:
            proof_candidate = config.candidate_formatter.format(proof, dp_obj)
            proof_context = config.context_formatter.format(proof, dp_obj)
            step_strs = [tokens2str(normalize(lex(s.step.text))) for s in proof.steps]
            example = ProofSelectionExample(proof_candidate, proof_context, step_strs)
            q.put(example)
        except CoqParseError:
            continue


ExampleFnArgs = tuple[
    ProofSelectionConfig, FileInfo, Queue[Optional[ProofSelectionExample]]
]


def get_example_args(
    config: ProofSelectionConfig,
    split: Split,
    q: Queue[Optional[ProofSelectionExample]],
) -> list[ExampleFnArgs]:
    args: list[ExampleFnArgs] = []
    for file in config.data_split.get_file_list(config.data_loc, split):
        args.append((config, file, q))
    return args


def writer(q: Queue[Optional[ProofSelectionExample]], out_file: str) -> None:
    num_examples_written = 0
    with open(out_file, "w") as fout:
        while True:
            example = q.get()
            match example:
                case ProofSelectionExample():
                    fout.write(json.dumps(example.to_json()) + "\n")
                    num_examples_written += 1
                    print(f"\rNum Examples: {num_examples_written}", end="")
                case None:
                    print()
                    return


if __name__ == "__main__":
    parser = argparse.ArgumentParser("Generate a proof retrieval dataset.")
    parser.add_argument(
        "conf_loc", help="Location of a configuration file for dataset generation."
    )
    parser.add_argument(
        "--num_procs",
        "-n",
        type=int,
        help="Number of processes to use to create the dataset.",
    )
    args = parser.parse_args(sys.argv[1:])
    num_procs = 2
    if args.num_procs:
        num_procs = args.num_procs
        if num_procs < 2:
            raise ValueError("Data processing needs at least 2 processes.")

    config = ProofSelectionConfig.load(args.conf_loc)

    if os.path.exists(config.out_loc):
        raise FileExistsError(f"{config.out_loc}")
    os.makedirs(config.out_loc)

    with mp.Manager() as manager:
        q: Queue[Optional[ProofSelectionExample]] = manager.Queue()
        with mp.Pool() as pool:
            for split in [Split.TEST, Split.VAL, Split.TRAIN]:
                split_args = get_example_args(config, split, q)
                raw_path = split_file_path(
                    config.out_loc,
                    split,
                    shuffled=False,
                    deduplicated=False,
                )
                deduped_path = split_file_path(
                    config.out_loc,
                    split,
                    shuffled=False,
                    deduplicated=True,
                )
                shuffled_path = split_file_path(
                    config.out_loc,
                    split,
                    shuffled=True,
                    deduplicated=True,
                )
                print(f"Processing {split.name}...")
                train_writer = pool.apply_async(writer, (q, raw_path))
                pool.starmap(examples_to_queue, split_args)
                q.put(None)
                train_writer.wait()
                num_duplicates = deduplicate(raw_path, deduped_path)
                print(f"Num Duplicates: {num_duplicates}")
                os.remove(raw_path)
                shuffle(deduped_path, shuffled_path)
                os.remove(deduped_path)

    conf_out_loc = os.path.join(config.out_loc, PROOF_CONF_NAME)
    shutil.copy(args.conf_loc, conf_out_loc)
