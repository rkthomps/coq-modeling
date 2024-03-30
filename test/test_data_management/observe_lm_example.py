import sys, os
import ipdb
import time
import cProfile
from tqdm import tqdm
from typing import Optional
from data_management.splits import DataSplit, Split, FileInfo, file_from_split
from data_management.dataset_file import DatasetFile
from data_management.sentence_db import SentenceDB 
from tactic_gen.lm_example import fmt_from_conf, move_fmt_to, LmFormatter, LmExample, ProofRetrievalFidFormatter
from tactic_gen.n_step_sampler import OneStepSampler


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

def one_file(
    file: str, formatter: LmFormatter 
) -> list[LmExample]:
    file_info, split = file_from_split(file, data_split)
    file_dp = file_info.get_dp(data_loc, sentence_db)
    print("Number of steps: ", count_steps(file_dp))
    examples: list[LmExample] = []
    for proof in file_dp.proofs:
        for i, step in enumerate(proof.steps):
            start = time.time()
            example = formatter.example_from_step(
                i,
                proof,
                dp_obj=file_dp,
                file_info=file_info,
                split=split,
                data_loc=data_loc,
                ground_truth_steps=None,
                key_record=None,
                cutoff_idx=None,
            )
            end = time.time()
            print("Step time:", end - start)
            examples.append(example)
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


def run_benchmarks(formatter: LmFormatter):
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
    #     #print("{:30s}: {:.2f}".format(file_info.file, end - start))


def run_proof_ret_benchmark():
    formatter = ProofRetrievalFidFormatter(PROOF_BANK_LOC, 20, OneStepSampler(), False, {}) 
    run_benchmarks(formatter)


def run_select_benchmark():
    fmt_conf = {
        "alias": "fid-premise",
        "premise_model_wrapper": {
            "alias": "local",
            "checkpoint_loc": "models/prem-select/checkpoint-15000" ,
            "vector_db_loc": "vector-dbs/prem-select",
        },
        "n_step_sampler": {
            "alias": "one",
        },
        "direct_num_steps": False,
    }
    formatter = fmt_from_conf(fmt_conf)
    move_fmt_to(formatter, "cuda")
    run_benchmarks(formatter)


if __name__ == "__main__":
    #cProfile.run("run_benchmark()")
    #cProfile.run("run_select_benchmark()")
    cProfile.run("run_proof_ret_benchmark()")


