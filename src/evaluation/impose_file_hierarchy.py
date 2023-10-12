
from typing import Any

import sys, os
import shutil
import argparse
import json
from tqdm import tqdm

from data_management.dataset_file import FILE_CONTEXT_NAME

FILE_MAPPING_NAME = "mapping.json"
DESIRED_PREFIX = "coq-dataset/repos"

def mapping_shape_correct(mapping: Any) -> bool:
    assert type(mapping) == dict
    for k, v in mapping.items():
        assert type(k) == str
        assert type(v) == str
    return True

def get_dot_v_file(file_data_loc: str) -> str:
    v_files: list[str] = []
    for subfile in os.listdir(file_data_loc):
        subfile_loc = os.path.join(file_data_loc, subfile)
        if subfile.endswith(".v"):
            v_files.append(subfile_loc)
    assert len(v_files) == 1
    return v_files[0]


def get_intended_path(file_data_loc: str) -> str:
    context_loc = os.path.join(file_data_loc, FILE_CONTEXT_NAME)
    with open(context_loc, "r") as fin:
        file_context_data = json.load(fin)
        intended_file_path = file_context_data["file"]
        assert type(intended_file_path) == str
    assert DESIRED_PREFIX in intended_file_path
    desired_prefix_idx = intended_file_path.index(DESIRED_PREFIX)
    return intended_file_path[desired_prefix_idx:]


def create_heirarchy(data_loc: str, hierarchy_loc: str) -> None:
    mapping: dict[str, str] = {}
    for combined_file_name in tqdm(os.listdir(data_loc)):
        combined_file_loc = os.path.join(data_loc, combined_file_name)
        v_loc = get_dot_v_file(combined_file_loc)
        intended_path = get_intended_path(combined_file_loc)
        full_relitive_intended_path = os.path.join(hierarchy_loc, intended_path)
        full_intended_path = os.path.abspath(full_relitive_intended_path)
        mapping[combined_file_name] = full_intended_path
        full_dirname = os.path.dirname(full_intended_path)
        if not os.path.exists(full_dirname):
            os.makedirs(full_dirname)
        shutil.copy(v_loc, full_intended_path)
    
    print("Writing mapping...")
    with open(os.path.join(hierarchy_loc, FILE_MAPPING_NAME), "w") as fout:
        fout.write(json.dumps(mapping, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Create a hierarchy of coq projects from raw data.")
    parser.add_argument("data_loc", help="Location of raw data directory.")
    parser.add_argument("hierarchy_loc", help="Location of new file hierarchy.")
    args = parser.parse_args(sys.argv[1:])
    create_heirarchy(args.data_loc, args.hierarchy_loc)