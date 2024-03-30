

import time
import os
from data_management.dataset_file import DatasetFile
from data_management.splits import DataSplit, Split
from data_management.sentence_db import SentenceDB
import cProfile


DP_LOC = os.path.join("raw-data", "coq-dataset", "data_points")
SENTENCES_DB_LOC = "sentences.db"

BENCHMARK_FILES = [
    "coq-community-corn-reals-stdlib-ConstructiveUniformCont.v",
    "AbsInt-CompCert-lib-Wfsimpl.v",
    "AbsInt-CompCert-lib-Zbits.v",
    "AbsInt-CompCert-powerpc-Archi.v",
    "AbsInt-CompCert-powerpc-Stacklayout.v",
    "AbsInt-CompCert-riscV-Archi.v",
    "AbsInt-CompCert-riscV-Stacklayout.v",
    "AbsInt-CompCert-x86-Asm.v",
    "AbsInt-CompCert-x86-Asmgenproof.v",
    "AbsInt-CompCert-x86-Asmgenproof1.v",
    "AbsInt-CompCert-x86-CombineOpproof.v",
    "AbsInt-CompCert-x86-ConstpropOpproof.v",
    "AbsInt-CompCert-x86-Conventions1.v",
    "AbsInt-CompCert-x86-Machregs.v",
    "AbsInt-CompCert-x86-NeedOp.v",
    "AbsInt-CompCert-x86-Op.v",
    "AbsInt-CompCert-x86-SelectLongproof.v",
    "AbsInt-CompCert-x86-SelectOpproof.v",
    "AbsInt-CompCert-x86-Stacklayout.v",
    "AbsInt-CompCert-x86-ValueAOp.v",
    "AbsInt-CompCert-x86_32-Archi.v",
    "AbsInt-CompCert-x86_64-Archi.v"
]

def run_benchmark() -> None:
    sentences_db = SentenceDB.load(SENTENCES_DB_LOC)
    for file in BENCHMARK_FILES:
        file_loc = os.path.join(DP_LOC, file)
        start = time.time()
        DatasetFile.load(file_loc, sentences_db)
        end = time.time()
        print("{:50s} {:10.2f}".format(file, end - start))



def run_split() -> None:
    sentences_db = SentenceDB.load(SENTENCES_DB_LOC)
    data_split = DataSplit.load("splits/final-split.json")
    data_loc = "raw-data/coq-dataset"
    for split in Split:
        for file_info in data_split.get_file_list(split):
            print(f"Processing {file_info.file}")
            file_info.get_dp(data_loc, sentences_db)

if __name__ == "__main__":
    cProfile.run("run_benchmark()")
    #cProfile.run("run_split()")
    #run_benchmark()



