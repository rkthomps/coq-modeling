import argparse
import sys, os
from pathlib import Path


from proof_retrieval.proof_vector_db import ProofVectorDB


def quick_validate(proof_db_loc: Path):
    pass


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "proof_db_loc", type=Path, help="Location of the proof database to validate"
    )

    args = parser.parse_args(sys.argv[1:])
    vector_db = ProofVectorDB.load(args.proof_db_loc)
