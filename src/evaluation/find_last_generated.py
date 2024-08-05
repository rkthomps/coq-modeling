from typing import Optional
import os
import json
import argparse
from pathlib import Path
from tqdm import tqdm

from data_management.splits import DataSplit, Split, FileInfo
from evaluation.eval_utils import ProofMap, create_eval_proof_map
from model_deployment.prove import summary_from_json


def get_eval_names(eval_loc: Path) -> list[str]:
    return [file for file in os.listdir(eval_loc) if file.endswith(".json")]


def search_for_name(
    file_info: FileInfo, proof_idx: int, eval_names: list[str]
) -> Optional[str]:
    for name in eval_names:
        assert file_info.dp_name.endswith(".v")
        fdp_name = file_info.dp_name[: -(len(".v"))]
        if not fdp_name in name:
            continue
        if name.endswith(f"{proof_idx}.json"):
            return name
    return None


def find_last(data_split_loc: Path, eval_loc: Path, ends: list[int]) -> list[int]:
    proof_map = create_eval_proof_map(
        Split.TEST, data_split_loc, SENTENCE_DB_LOC, DATA_LOC
    )
    eval_names = get_eval_names(eval_loc)
    last_generated: list[int] = []
    for end in ends:
        cur = end
        while 0 <= cur:
            if not cur < len(proof_map.proofs):
                cur -= 1
                continue
            file_info, idx = proof_map.proofs[cur]
            eval_name = search_for_name(file_info, idx, eval_names)
            if eval_name is None:
                cur -= 1
                continue
            with open(eval_loc / eval_name) as fin:
                json_summary = json.load(fin)
                summary = summary_from_json(json_summary)
                if summary.model_time is None:
                    cur -= 1
                    continue
            break
        last_generated.append(cur)
    return last_generated


def find_missing(data_split_loc: Path, eval_loc: Path) -> list[int]:
    proof_map = create_eval_proof_map(
        Split.TEST, data_split_loc, SENTENCE_DB_LOC, DATA_LOC
    )
    eval_names = get_eval_names(eval_loc)
    missing: list[int] = []
    for i, (file_info, idx) in tqdm(enumerate(proof_map.proofs)):
        eval_name = search_for_name(file_info, idx, eval_names)
        if eval_name is None:
            missing.append(i)
            continue
        with open(eval_loc / eval_name) as fin:
            json_summary = json.load(fin)
            summary = summary_from_json(json_summary)
            if summary.model_time is None:
                missing.append(i)
    return missing


DATA_LOC = Path("raw-data/coq-dataset")
SENTENCE_DB_LOC = Path("raw-data/coq-dataset/sentences.db")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("data_split_loc")
    parser.add_argument("eval_loc")
    parser.add_argument("ends", type=int, nargs="+")
    args = parser.parse_args()

    data_split_loc = Path(args.data_split_loc)
    eval_loc = Path(args.eval_loc)
    assert data_split_loc.exists()
    assert eval_loc.exists()

    data_split = DataSplit.load(data_split_loc)
    ends = args.ends

    # lasts = find_last(data_split_loc, eval_loc, ends)
    # print(lasts)

    missing = find_missing(data_split_loc, eval_loc)
    print(missing)
