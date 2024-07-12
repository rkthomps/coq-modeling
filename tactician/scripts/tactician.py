import sys
import os
import json
import subprocess
import shutil
import tqdm

# Avoids error for missing API key
os.environ["OPENAI_API_KEY"] = "PLACEHOLDER"

from pathlib import Path
from data_management.splits import (
    DataSplit, Split, SentenceDB, FileInfo, Proof
)
from concurrent.futures import ThreadPoolExecutor, as_completed


final = DataSplit.load(Path("../../splits/final-split.json"))
random = DataSplit.load(Path("../../splits/random-split.json"))


data_loc = Path("../../raw-data/coq-dataset")
data_points_loc = Path("data-points/")
sentence_db_loc = Path("../../raw-data/coq-dataset/sentences.db")
sentence_db = SentenceDB.load(sentence_db_loc)

results = Path("results/")

def test_proof(
    proof: Proof,
    file_path: Path, 
    original_file_path: Path, 
    proof_file: Path, 
    file_info: FileInfo, 
    i: int
):
    new_path = Path(os.path.dirname(os.path.realpath(original_file_path))) / f"{i}.v"
    shutil.copy(proof_file, new_path)
    run = subprocess.run(
        ["coqc", original_file_path], 
        stdout=subprocess.PIPE, 
        stderr=subprocess.PIPE,
        timeout=60 * 10 # 10 minutes
    )
    
    with open(results / f"{file_path}_{i}.json", "w") as f:
        f.write(json.dumps({
            "file": file_info.file,
            "theorem": proof.theorem.term.text,
            "success": "Tactician found a proof!" in run.stdout.decode("utf-8"),
            "stdout": run.stdout.decode("utf-8"),
            "stderr": run.stderr.decode("utf-8")
        }, indent=2))
    os.remove(new_path)


def tactician_data_points_in_split(
    data_split: DataSplit, split: Split, n_cores: int = 1
):
    pool = ThreadPoolExecutor(n_cores)
    futures = []

    for file_info in data_split.get_file_list(split):
        file_path = file_info.file.replace("/", "_")
        file_data_point = file_info.get_dp(data_loc, sentence_db)
        original_file_path = data_loc / file_info.file

        for i, proof in enumerate(file_data_point.proofs):
            if proof.is_proof_independent():
                proof_file = data_points_loc / file_path / f"{i}.v"
                if not os.path.exists(proof_file):
                    continue
                futures.append(pool.submit(
                    test_proof, 
                    proof, 
                    file_path, 
                    original_file_path, 
                    proof_file, 
                    file_info, 
                    i
                ))

    for future in tqdm.tqdm(as_completed(futures), total=len(futures)):
        future.result()


if __name__ == "__main__":
    if not os.path.exists(results):
        os.makedirs(results)

    if len(sys.argv) > 1:
        n_cores = int(sys.argv[1])
    else:
        n_cores = 1

    tactician_data_points_in_split(final, Split.TEST, n_cores=n_cores)
