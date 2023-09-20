

import sys, os
import argparse
import subprocess
from impose_file_hierarchy import NEW_ROOT_NAME 

PROJECT_NAME = "_CoqProject"
MAKEFILE_NAME = "CoqMakefile"
MAKEFILE_CONF_NAME = "CoqMakefile.conf"
SPECIAL_FILES = [PROJECT_NAME, MAKEFILE_NAME, MAKEFILE_CONF_NAME]

COQ_PROJECT_PREFIX = "-R theories CoqRepos"

def clean_directory(dir_loc: str) -> None:
    parent_loc = os.path.dirname(dir_loc)
    for s_fname in SPECIAL_FILES:
        s_loc = os.path.join(parent_loc, s_fname)
        if os.path.exists(s_loc):
            os.remove(s_loc)


def get_coq_project_contents(dir_loc: str) -> str:
    dir_name = os.path.basename(dir_loc)
    return f"-R {dir_name} MyProject\n{dir_name}"


def compile_directory(dir_loc: str) -> None:
    clean_directory(dir_loc)
    parent_dir = os.path.dirname(dir_loc)
    os.chdir(parent_dir)
    coq_project_loc = os.path.join(parent_dir, PROJECT_NAME)
    with open(coq_project_loc, "w") as fout:
        fout.write(get_coq_project_contents(dir_loc))
    p_create_make = subprocess.run(["coq_makefile", "-f", PROJECT_NAME, "-o", MAKEFILE_NAME])
    assert p_create_make.returncode == 0
    p_make = subprocess.run(["make", "-f", MAKEFILE_NAME])
    if p_make.returncode != 0:
        for subdir_name in os.listdir(dir_loc):
            subdir_loc = os.path.join(dir_loc, subdir_name)
            if os.path.isdir(subdir_loc):
                compile_directory(subdir_loc)


if __name__ == "__main__":
    parser = argparse.ArgumentParser("Compile a set of coq repos.")
    parser.add_argument("tree_parent_loc", help="Location of the output directory from impose_file_hierarchy.py.")
    args = parser.parse_args(sys.argv[1:])
    compile_target = os.path.join(args.tree_parent_loc, NEW_ROOT_NAME)
    compile_target_full_path = os.path.abspath(compile_target)
    compile_directory(compile_target_full_path)
