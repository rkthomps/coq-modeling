import os
import sys
import tqdm
import json

# Avoids error for missing API key
os.environ["OPENAI_API_KEY"] = "PLACEHOLDER"

from pathlib import Path
from data_management.splits import DataSplit, Split, SentenceDB, FileInfo, DatasetFile
from model_deployment.prove import get_proof_info, normalize
from concurrent.futures import ThreadPoolExecutor, as_completed


final = DataSplit.load(Path("/home/nfsaavedra/coq-modeling/tactician/cutoff-eval/cutoff-8.18.json"))
random = DataSplit.load(Path("../../splits/random-split.json"))


data_loc = Path("../../raw-data/coq-dataset")
data_points_loc = Path("data-points")
sentence_db_loc = Path("sentences.db")
sentence_db = SentenceDB.load(sentence_db_loc)


def generate_data_points_in_file(file_info: FileInfo, file_data_point: DatasetFile):
    file_path = file_info.file.replace("/", "_")

    for i, proof in enumerate(file_data_point.proofs):
        if proof.is_proof_independent():

            occurrence = 0
            for p in file_data_point.proofs[:i]:
                if normalize(proof.theorem.term.text) == normalize(p.theorem.term.text):
                    occurrence += 1

            proof_info = get_proof_info(data_loc, file_info, proof.theorem, occurrence)
            prefix = "".join([s.text for s in proof_info.prefix_steps])
            # prefix += "\nsynth.\nQed.\n"
            proof_file = data_points_loc / file_path / f"{i}.v"
            with open(proof_file, "w") as f:
                f.write(prefix)


def generate_data_points_in_split(data_split: DataSplit, split: Split, n_cores: int):
    pool = ThreadPoolExecutor(n_cores)
    futures = []

    print("Initializing...")
    for file_info in data_split.get_file_list(split):
        file_path = file_info.file.replace("/", "_")
        file_data_point = file_info.get_dp(data_loc, sentence_db)

        if not os.path.exists(data_points_loc / file_path):
            os.makedirs(data_points_loc / file_path)
        with open(data_points_loc / file_path / "info.json", "w") as f:
            json.dump({"path": file_info.file}, f)

        futures.append(
            pool.submit(generate_data_points_in_file, file_info, file_data_point)
        )

    for future in tqdm.tqdm(as_completed(futures), total=len(futures)):
        future.result()


if __name__ == "__main__":
    if len(sys.argv) > 1:
        n_cores = int(sys.argv[1])
    else:
        n_cores = 1

    if not os.path.exists(data_points_loc):
        os.makedirs(data_points_loc)
    generate_data_points_in_split(final, Split.TEST, n_cores)
