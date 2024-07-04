import os
import shutil
import tqdm

# Avoids error for missing API key
os.environ["OPENAI_API_KEY"] = "PLACEHOLDER"

from pathlib import Path
from data_management.splits import DataSplit, Split, SentenceDB


final = DataSplit.load(Path("../../splits/final-split.json"))
random = DataSplit.load(Path("../../splits/random-split.json"))


data_loc = Path("../../raw-data/coq-dataset")
data_points_loc = Path("data-points/")
sentence_db_loc = Path("../../raw-data/coq-dataset/sentences.db")
sentence_db = SentenceDB.load(sentence_db_loc)


def tactician_data_points_in_split(data_split: DataSplit, split: Split):
    for file_info in tqdm.tqdm(data_split.get_file_list(split)):
        file_path = file_info.file.replace("/", "_")
        file_data_point = file_info.get_dp(data_loc, sentence_db)
        original_file_path = data_loc / file_info.file
        print(original_file_path)

        for i, proof in enumerate(file_data_point.proofs):
            if proof.is_proof_independent():
                proof_file = data_points_loc / file_path / f"{i}.v"
                if not os.path.exists(proof_file):
                    continue

                shutil.copy(original_file_path, original_file_path.with_suffix(".backup"))
                shutil.copy(proof_file, original_file_path)
                os.system(f"coqc {original_file_path}")
                shutil.copy(original_file_path.with_suffix(".backup"), original_file_path)
                os.remove(original_file_path.with_suffix(".backup"))
                exit(0)

if __name__ == "__main__":
    tactician_data_points_in_split(final, Split.TEST)
