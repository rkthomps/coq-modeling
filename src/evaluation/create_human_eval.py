import os
import argparse
from pathlib import Path
import json

from data_management.dataset_file import DatasetFile
from data_management.sentence_db import SentenceDB
from data_management.splits import DataSplit, Split, REPOS_NAME
from evaluation.cross_tool_analysis import GeneralResult


def clean_human_path(human_path: Path) -> Path:
    assert human_path.parts[0] == REPOS_NAME
    rel_human_path = human_path.relative_to(Path(REPOS_NAME))
    return GeneralResult.strip_path(rel_human_path)


def get_num_deps(self, dataset_file: DatasetFile) -> tuple[int, int]:
    dep_files: set[str] = set()
    for p in dataset_file.out_of_file_avail_premises:
        dep_files.add(p.file_path)
    return len(dep_files), len(dataset_file.dependencies)


def create_human_eval(
    data_split_loc: Path, data_loc: Path, sentence_db_loc: Path, save_loc: Path
):
    data_split = DataSplit.load(data_split_loc)
    sentence_db = SentenceDB.load(sentence_db_loc)

    for file_info in data_split.get_file_list(Split.TEST):
        file_dp = file_info.get_dp(data_loc, sentence_db)
        num_deps, num_proj_deps = get_num_deps(file_info, file_dp)
        for i, proof in enumerate(file_dp.proofs):
            if not proof.is_proof_independent():
                continue
            proof_result = GeneralResult(
                clean_human_path(Path(file_info.file)),
                Path(file_info.file),
                proof.theorem.term.text,
                0,
                True,
                proof.proof_text_to_string(include_theorem=False),
                num_deps,
                num_proj_deps,
            )
            save_name = (file_info.dp_name + "-" + str(i) + ".json")[-255:]
            with open(save_loc / save_name, "w") as fout:
                json.dump(proof_result.to_json(), fout, indent=2)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("data_split_loc")
    parser.add_argument("data_loc")
    parser.add_argument("sentence_db_loc")
    parser.add_argument("save_loc")

    args = parser.parse_args()

    data_split_loc = Path(args.data_split_loc)
    data_loc = Path(args.data_loc)
    sentence_db_loc = Path(args.sentence_db_loc)
    save_loc = Path(args.save_loc)

    assert data_split_loc.exists()
    assert data_loc.exists()
    assert sentence_db_loc.exists()
    if save_loc.exists():
        raise FileExistsError(f"{save_loc} exists.")
    os.makedirs(save_loc)

    create_human_eval(data_split_loc, data_loc, sentence_db_loc, save_loc)
