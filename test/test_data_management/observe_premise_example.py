import sys, os
import ipdb
import time
import cProfile
from tqdm import tqdm
from typing import Optional
from data_management.splits import DataSplit, Split, FileInfo, file_from_split
from data_management.dataset_file import DatasetFile
from data_management.sentence_db import SentenceDB
from premise_selection.premise_example import PremiseTrainingExample
from premise_selection.create_premise_example import premise_training_examples_from_step
from model_deployment.premise_model_wrapper import (
    LocalPremiseModelWrapper,
    premise_wrapper_from_conf,
    move_prem_wrapper_to,
)


SENTENCES_LOC = "sentences.db"
PROOF_BANK_LOC = "proof-goals"

data_split = DataSplit.load("splits/final-split.json")
data_loc = "raw-data/coq-dataset"
sentence_db = SentenceDB.load(SENTENCES_LOC)


def count_steps(file_dp: DatasetFile) -> int:
    n_steps = 0
    for proof in file_dp.proofs:
        n_steps += len(proof.steps)
    return n_steps


def one_file(file: str, wrapper: LocalPremiseModelWrapper):
    file_info, split = file_from_split(file, data_split)
    file_dp = file_info.get_dp(data_loc, sentence_db)
    print("Number of steps: ", count_steps(file_dp))
    examples: list[PremiseTrainingExample] = []
    cur_step = 0
    for proof in file_dp.proofs:
        for i, step in enumerate(proof.steps):
            start = time.time()
            premise_training_examples_from_step(step, proof, file_dp, 3, wrapper)
            end = time.time()
            cur_step += 1
            print(cur_step, "Step time:", end - start)
    return examples


files = [
    "repos/coq-community-gaia/theories/sets/sset9.v",
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


def run_benchmarks(wrapper: LocalPremiseModelWrapper):
    for file in files:
        start = time.time()
        one_file(file, wrapper)
        end = time.time()
        print("{:30s}: {:.2f}".format(file, end - start))

    # for file_info in reversed(data_split.get_file_list(Split.TRAIN)):
    #     print(file_info.file + "       ", end="", flush=True)
    #     start = time.time()
    #     one_file(file_info.file, formatter)
    #     end = time.time()
    #     print("{:30s}: {:.2f}".format(file_info.file, end - start))


def run_select_benchmark():
    conf = {
        "alias": "local",
        "checkpoint_loc": "models/prem-select/checkpoint-15000",
        "vector_db_loc": "vector-dbs/prem-select",
    }
    wrapper = LocalPremiseModelWrapper.from_conf(conf)
    move_prem_wrapper_to(wrapper, "cuda")
    run_benchmarks(wrapper)


if __name__ == "__main__":
    # cProfile.run("run_benchmark()")
    cProfile.run("run_select_benchmark()")
    # cProfile.run("run_rerank_benchmark()")
    # cProfile.run("run_proof_ret_benchmark()")
