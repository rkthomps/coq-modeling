import os

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


def find_missing_data_points_in_split(data_split: DataSplit, split: Split):
    for file_info in data_split.get_file_list(split):
        file_path = file_info.file.replace("/", "_")
        file_data_point = file_info.get_dp(data_loc, sentence_db)

        for i, proof in enumerate(file_data_point.proofs):
            if proof.is_proof_independent():
                proof_file = data_points_loc / file_path / f"{i}.v"
                if not os.path.exists(proof_file):
                    print(proof_file)
                    print(proof.theorem.term.text)
                    print()


if __name__ == "__main__":
    if not os.path.exists(data_points_loc):
        os.makedirs(data_points_loc)
    find_missing_data_points_in_split(final, Split.TEST)
