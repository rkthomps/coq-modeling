import sys, os
import ipdb
import time
import cProfile
from tqdm import tqdm
from pathlib import Path
from typing import Optional
from premise_selection.rerank_example import RerankExample
from premise_selection.rerank_formatter import RerankFormatter
from premise_selection.premise_filter import PremiseFilterConf
from model_deployment.premise_client import TFIdfClient, TFIdfConf
from data_management.splits import DataSplit, Split, FileInfo, file_from_split
from data_management.dataset_file import DatasetFile
from data_management.sentence_db import SentenceDB
from tactic_gen.n_step_sampler import OneStepSampler


SENTENCES_LOC = Path("sentences.db")
PROOF_BANK_LOC = Path("proof-goals")
DATA_SPLIT_LOC = Path("splits/final-split.json")
DATA_LOC = Path("raw-data/coq-dataset")

data_split = DataSplit.load(DATA_SPLIT_LOC)
sentence_db = SentenceDB.load(SENTENCES_LOC)


def count_steps(file_dp: DatasetFile) -> int:
    n_steps = 0
    for proof in file_dp.proofs:
        n_steps += len(proof.steps)
    return n_steps


def one_file(file: str, formatter: RerankFormatter) -> list[RerankExample]:
    file_info, split = file_from_split(file, data_split)
    file_dp = file_info.get_dp(DATA_LOC, sentence_db)
    print("Number of steps: ", count_steps(file_dp))
    examples: list[RerankExample] = []
    for proof in file_dp.proofs:
        for step in proof.steps:
            start = time.time()
            example = formatter.examples_from_step(
                step,
                proof,
                file_dp,
            )
            end = time.time()
            print("Step time:", end - start)
            examples.extend(example)
    return examples


files = [
    "repos/coq-community-corn/reals/stdlib/ConstructiveUniformCont.v",
    "repos/AbsInt-CompCert/x86/Asm.v",
    "repos/AbsInt-CompCert/x86/Asmgenproof.v",
    # "repos/AbsInt-CompCert/x86/Asmgenproof1.v",
    # "repos/AbsInt-CompCert/x86/CombineOpproof.v",
    # "repos/AbsInt-CompCert/x86/ConstpropOpproof.v",
    # "repos/AbsInt-CompCert/x86/Conventions1.v",
    # "repos/AbsInt-CompCert/x86/Machregs.v",
    # "repos/AbsInt-CompCert/x86/NeedOp.v",
    # "repos/AbsInt-CompCert/x86/Op.v",
    # "repos/AbsInt-CompCert/x86/SelectLongproof.v",
    # "repos/AbsInt-CompCert/x86/SelectOpproof.v",
    # "repos/AbsInt-CompCert/x86/Stacklayout.v",
    # "repos/AbsInt-CompCert/x86/ValueAOp.v",
]


def run_benchmarks(formatter: RerankFormatter):
    for file in files:
        start = time.time()
        one_file(file, formatter)
        end = time.time()
        print("{:30s}: {:.2f}".format(file, end - start))

    # for file_info in reversed(data_split.get_file_list(Split.TRAIN)):
    #     print(file_info.file + "       ", end="", flush=True)
    #     start = time.time()
    #     one_file(file_info.file, formatter)
    #     end = time.time()
    #     print(end - start)
    # print("{:30s}: {:.2f}".format(file_info.file, end - start))


def run_benchmark():
    premise_filter_conf = PremiseFilterConf([], [], [])
    tfidf_conf = TFIdfConf("basic", "basic", premise_filter_conf)
    formatter = RerankFormatter(TFIdfClient.from_conf(tfidf_conf), 256, 4)
    run_benchmarks(formatter)


if __name__ == "__main__":
    cProfile.run("run_benchmark()")
