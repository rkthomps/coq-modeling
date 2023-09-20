
from typing import Any

import sys, os
import shutil
import argparse
import re
import pdb
import json
from tqdm import tqdm


NEW_ROOT_NAME = "coq-repos"
FILE_MAPPING_NAME = "mapping.json"

def mapping_shape_correct(mapping: Any) -> bool:
    assert type(mapping) == dict
    for k, v in mapping.items():
        assert type(k) == str
        assert type(v) == str
    return True


class FileTree:
    def __init__(self, value: str) -> None:
        self.value = value
        self.children: list[FileTree] = []

    def add(self, path: list[str]) -> None:
        if len(path) == 0:
            return
        assert path[0] == self.value
        if len(path) == 1:
            return
        for c in self.children:
            if path[1] == c.value:
                c.add(path[1:])
                return
        self.children.append(FileTree(path[1]))
        self.children[-1].add(path[1:])

    def get_path(self, file_tokens: list[str]) -> str:
        return "/".join(file_tokens)


def prep_file_name(file_name: str) -> list[str]:
    name_match = re.match(r"-coq-dataset-repos-(.*)", file_name)
    assert name_match is not None
    remainder, = name_match.groups()
    dir_list = [NEW_ROOT_NAME] + remainder.split("-")
    return dir_list


def find_coq_file(coq_file_data_dir: str) -> str:
    for filename in os.listdir(coq_file_data_dir):
        if filename.endswith(".v"):
            return os.path.join(coq_file_data_dir, filename)
    raise ValueError("Directory did not have coq file.")


def create_heirarchy(data_loc: str, hierarchy_loc: str) -> None:
    new_root_name = "coq-repos"
    ftree = FileTree(new_root_name)

    print("Indexing Files...")
    for orig_name in tqdm(os.listdir(data_loc)):
        if not orig_name.endswith(".v"):
            continue
        dir_list = prep_file_name(orig_name) 
        ftree.add(dir_list)

    print("Copying files...")
    path_mappings: dict[str, str] = {}
    for orig_name in tqdm(os.listdir(data_loc)):
        if not orig_name.endswith(".v"):
            continue
        dir_list = prep_file_name(orig_name)
        file_path = ftree.get_path(dir_list)
        full_file_path = os.path.abspath(os.path.join(hierarchy_loc, file_path))
        path_mappings[orig_name] = full_file_path
        squeezed_dirname = os.path.dirname(full_file_path)
        if not os.path.exists(squeezed_dirname):
            os.makedirs(squeezed_dirname)
        orig_coq_file_path = find_coq_file(os.path.join(data_loc, orig_name))
        shutil.copy(orig_coq_file_path, squeezed_dirname)

    print("Writing mapping...")
    with open(os.path.join(hierarchy_loc, FILE_MAPPING_NAME), "w") as fout:
        fout.write(json.dumps(path_mappings, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Create a hierarchy of coq projects from raw data.")
    parser.add_argument("data_loc", help="Location of raw data directory.")
    parser.add_argument("hierarchy_loc", help="Location of new file hierarchy.")
    args = parser.parse_args(sys.argv[1:])
    create_heirarchy(args.data_loc, args.hierarchy_loc)

