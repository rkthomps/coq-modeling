

import sys, os
import re
import argparse
import subprocess
from impose_file_hierarchy import DESIRED_PREFIX

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


def this_or_sub_has_dash_or_dot(dir_loc: str) -> bool:
    bad_pattern = re.compile(r"[-.]")
    if bad_pattern.search(os.path.basename(dir_loc)):
        return True
    for files, dirs, root in os.walk(dir_loc):
        for dir in dirs:
            if bad_pattern.search(dir):
                return True
    return False


def compile_directory(dir_loc: str, num_cores: int) -> None:
    if not this_or_sub_has_dash_or_dot(dir_loc):
        clean_directory(dir_loc)
        parent_loc = os.path.dirname(dir_loc)
        os.chdir(parent_loc)
        coq_project_loc = os.path.join(parent_loc, PROJECT_NAME)
        with open(coq_project_loc, "w") as fout:
            fout.write(get_coq_project_contents(dir_loc))
        p_create_make = subprocess.run(["coq_makefile", "-f", PROJECT_NAME, "-o", MAKEFILE_NAME])
        assert p_create_make.returncode == 0
        p_make = subprocess.run(["make", "-j", str(num_cores), "-f", MAKEFILE_NAME])
        if p_make.returncode == 0:
            return

    for subdir_name in os.listdir(dir_loc):
        subdir_loc = os.path.join(dir_loc, subdir_name)
        if os.path.isdir(subdir_loc):
            compile_directory(subdir_loc, num_cores)


if __name__ == "__main__":
    parser = argparse.ArgumentParser("Compile a set of coq repos.")
    parser.add_argument("tree_parent_loc", help="Location of the output directory from impose_file_hierarchy.py.")
    parser.add_argument("--num_cores", "-n", type=int, help="Number of jobs to use when running make.")
    args = parser.parse_args(sys.argv[1:])

    num_cores = 1
    if args.num_cores is not None:
        num_cores = args.num_cores

    rel_base_directory = os.path.join(args.tree_parent_loc, DESIRED_PREFIX)
    base_directory = os.path.abspath(rel_base_directory)
    for repo_name in os.listdir(base_directory):
        repo_loc = os.path.join(base_directory, repo_name)
        if not os.path.isdir(repo_loc):
            continue
        abs_repo_loc = os.path.abspath(repo_loc)
        compile_directory(abs_repo_loc, num_cores)
