from pathlib import Path
import pickle

from data_management.splits import DataSplit, get_all_files, FileInfo
from data_management.sentence_db import SentenceDB

from proof_retrieval.proof_idx import ProofStateIdx


METADATA_LOC = Path("data/vector-dbs/codebert-proof-state-vector-db/metadata.pkl")
with METADATA_LOC.open("rb") as fin:
    metadata = pickle.load(fin)

proof_idx: ProofStateIdx = metadata["proof_idx"]

DATA_SPLIT_LOCS = [
    Path("splits/random-split.json"),
    Path("splits/final-split.json"),
]

DATA_LOC = Path("raw-data/coq-dataset")
SENTENCE_DB_LOC = Path("raw-data/coq-dataset/sentences.db")

LOOKING_FOR = "coq-community-stalmarck-theories-Algorithm-memoryImplement.v"


data_splits = [DataSplit.load(p) for p in DATA_SPLIT_LOCS]
all_files = get_all_files(data_splits)


def find_file(file_infos: list[FileInfo], file_name: str) -> FileInfo:
    for f_info in file_infos:
        if f_info.dp_name == file_name:
            return f_info
    raise ValueError(f"Could not find file {file_name}")


sentence_db = SentenceDB.load(SENTENCE_DB_LOC)
f_info = find_file(all_files, LOOKING_FOR)

file_dp = f_info.get_dp(DATA_LOC, sentence_db)
print(f"File dp name: {file_dp.dp_name}; File info name: {f_info.dp_name}")
print("Theyre equal: ", file_dp.dp_name == f_info.dp_name)


for proof in file_dp.proofs:
    for i, step in enumerate(proof.steps):
        step_hash = proof_idx.hash_proof_step(i, proof, file_dp.dp_name)
        assert proof_idx.contains(step_hash)
