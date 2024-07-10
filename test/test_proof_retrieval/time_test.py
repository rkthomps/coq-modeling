from pathlib import Path
from dataclasses import dataclass
import time

import cProfile

from data_management.dataset_file import Proof
from data_management.sentence_db import SentenceDB
from data_management.splits import DataSplit, file_from_split
from proof_retrieval.proof_retriever import ProofDBQuery, DeepProofRetrieverClient
from proof_retrieval.proof_ret_wrapper import ProofRetWrapper

from util.util import get_basic_logger

_logger = get_basic_logger(__name__)


DATA_SPLIT_LOC = Path("splits/final-split.json")
DATA_LOC = Path("raw-data/coq-dataset")
SENTENCE_DB_LOC = Path("raw-data/coq-dataset/sentences.db")

MODEL_NAME = "microsoft/codebert-base"
VECTOR_DB_LOC = Path("data/vector-dbs/codebert-proof-state-vector-db")
MAX_SEQ_LEN = 512

TEST_FILES = [
    "repos/coq-community-corn/reals/stdlib/ConstructiveUniformCont.v",
    "repos/AbsInt-CompCert/x86/Asm.v",
    "repos/AbsInt-CompCert/x86/Asmgenproof.v",
]


_logger.info("Prepping...")
data_split = DataSplit.load(DATA_SPLIT_LOC)
sentence_db = SentenceDB.load(SENTENCE_DB_LOC)

file_infos = [file_from_split(file, data_split) for file in TEST_FILES]

proof_ret_wrapper = ProofRetWrapper.from_model_name(
    MODEL_NAME, MAX_SEQ_LEN, VECTOR_DB_LOC
)
proof_ret_client = DeepProofRetrieverClient(
    [], proof_ret_wrapper.proof_vector_db.proof_idx, sentence_db, DATA_LOC, 20
)
_logger.info("Done Prepping")


def run_benchmark():
    for f_info, s in file_infos:
        file_dp = f_info.get_dp(DATA_LOC, sentence_db)
        for proof in file_dp.proofs:
            for i, step in enumerate(proof.steps):
                start = time.time()
                proof_query = ProofDBQuery(i, proof, file_dp.dp_name)

                # Copied (ugly, i know)
                hashed_step_idx = proof_ret_client.proof_idx.hash_proof_step(
                    i, proof, file_dp.dp_name
                )
                if proof_ret_client.proof_idx.contains(hashed_step_idx):
                    query_step_idx = proof_ret_client.proof_idx.get_idx(hashed_step_idx)
                else:
                    query_step_idx = None
                # HARD CODED
                goal_str = ProofDBQuery(i, proof, file_dp.dp_name).format()
                available_proofs_and_objs = proof_ret_client.get_available_proofs(
                    proof, file_dp
                )
                available_proof_idxs: list[int] = []
                available_proof_steps: list[tuple[Proof, int]] = []
                for p, dep_obj in available_proofs_and_objs:
                    for i, step in enumerate(p.steps):
                        try:
                            step_hash = proof_ret_client.proof_idx.hash_proof_step(
                                i, p, dep_obj.dp_name
                            )
                            step_idx = proof_ret_client.proof_idx.get_idx(step_hash)
                            available_proof_idxs.append(step_idx)
                            available_proof_steps.append((p, i))
                        except KeyError:
                            _logger.error(
                                f"Could not find step {i} in {dep_obj.dp_name}"
                            )
                end = time.time()
                _logger.info(f"Step time: {end - start}")


if __name__ == "__main__":
    cProfile.run("run_benchmark()")
