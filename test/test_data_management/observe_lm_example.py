import sys, os
import ipdb
import time
import cProfile
from tqdm import tqdm
from typing import Optional
from data_management.splits import DataSplit, Split, FileInfo, file_from_split
from data_management.dataset_file import DatasetFile
from data_management.sentence_db import SentenceDB 
from tactic_gen.lm_example import fmt_from_conf, LmFormatter, LmExample, ProofRetrievalFidFormatter
from tactic_gen.n_step_sampler import OneStepSampler


SENTENCES_LOC = "sentences.db"
PROOF_BANK_LOC = "proof-goals"

def one_file(
    file: str, data_split: DataSplit, sentence_db: SentenceDB, data_loc: str, formatter: ProofRetrievalFidFormatter 
) -> list[LmExample]:
    file_info, split = file_from_split(file, data_split)
    file_dp = file_info.get_dp(data_loc, sentence_db)
    examples: list[LmExample] = []
    for proof in file_dp.proofs:
        for i, step in enumerate(proof.steps):
            start = time.time()
            example = formatter.example_from_step(
                i, proof, file_dp, file_info
            )
            end = time.time()
            print("Step time:", end - start)
            examples.append(example)
    return examples

files = [
    "repos/AbsInt-CompCert/x86/Asm.v",
    "repos/AbsInt-CompCert/x86/Asmgenproof.v",
    "repos/AbsInt-CompCert/x86/Asmgenproof1.v",
    "repos/AbsInt-CompCert/x86/CombineOpproof.v",
    "repos/AbsInt-CompCert/x86/ConstpropOpproof.v",
    "repos/AbsInt-CompCert/x86/Conventions1.v",
    "repos/AbsInt-CompCert/x86/Machregs.v",
    "repos/AbsInt-CompCert/x86/NeedOp.v",
    "repos/AbsInt-CompCert/x86/Op.v",
    "repos/AbsInt-CompCert/x86/SelectLongproof.v",
    "repos/AbsInt-CompCert/x86/SelectOpproof.v",
    "repos/AbsInt-CompCert/x86/Stacklayout.v",
    "repos/AbsInt-CompCert/x86/ValueAOp.v",
]

formatter = ProofRetrievalFidFormatter(PROOF_BANK_LOC, 20, OneStepSampler(), False, {}) 

data_split = DataSplit.load("splits/final-split.json")

data_loc = "raw-data/coq-dataset"

sentence_db = SentenceDB.load(SENTENCES_LOC)

def run_benchmark():
    for file in files:
        start = time.time()
        one_file(file, data_split ,sentence_db, data_loc, formatter)
        end = time.time()
        print("{:30s}: {:.2f}".format(file, end - start))

if __name__ == "__main__":
    cProfile.run("run_benchmark()")


