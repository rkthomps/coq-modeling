import os
import json
import argparse
from pathlib import Path
from coqstoq import Split, get_theorem_list
from util.coqstoq_utils import str2split
from evaluation.find_coqstoq_idx import get_thm_desc
from data_management.dataset_file import DatasetFile
from data_management.sentence_db import SentenceDB
from tqdm import tqdm


def get_num_deps(dataset_file: DatasetFile) -> tuple[int, int]:
    dep_files: set[str] = set()
    for p in dataset_file.out_of_file_avail_premises:
        dep_files.add(p.file_path)
    return len(dep_files) - 1, len(dataset_file.dependencies)  # exclude the file itself


def get_thm_dep_list(
    coqstoq_loc: Path, split: Split, data_loc: Path, sentence_db: SentenceDB
) -> list[int]:
    thms = get_theorem_list(split, coqstoq_loc)
    cached_path_deps: dict[Path, int] = {}
    dep_list: list[int] = []
    for thm in tqdm(thms):
        thm_path = thm.project.workspace.name / thm.path
        if thm_path in cached_path_deps:
            dep_list.append(cached_path_deps[thm_path])
        else:
            thm_desc = get_thm_desc(thm, data_loc, sentence_db)
            assert thm_desc is not None
            num_deps, _ = get_num_deps(thm_desc.dp)
            dep_list.append(num_deps)
            cached_path_deps[thm_path] = num_deps
    return dep_list


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--coqstoq_loc", type=str, required=True)
    parser.add_argument("--split", type=str, required=True)
    parser.add_argument("--data_loc", type=str, required=True)
    parser.add_argument("--sentence_db_loc", type=str, required=True)
    parser.add_argument("--save_loc", type=str, required=True)

    args = parser.parse_args()
    coqstoq_loc = Path(args.coqstoq_loc)
    split = str2split(args.split)
    data_loc = Path(args.data_loc)
    sentence_db_loc = Path(args.sentence_db_loc)
    save_loc = Path(args.save_loc)

    assert not save_loc.exists()

    sentence_db = SentenceDB.load(sentence_db_loc)
    dep_list = get_thm_dep_list(coqstoq_loc, split, data_loc, sentence_db)

    os.makedirs(save_loc.parent, exist_ok=True)
    with save_loc.open("w") as fout:
        json.dump(dep_list, fout, indent=2)
