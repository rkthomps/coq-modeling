
# My friend for compiling coq: https://coq.inria.fr/refman/practical-tools/utilities.html
# Generate make file:  coq_makefile -f _CoqProject -o CoqMakefile
# Run make file: make -f CoqMakefile

import sys, os
import argparse
import subprocess


COQ_PROJECT_NAME = "_CoqProject"
COQ_MAKEFIE_NAME = "CoqMakeile"
COQ_CONF_NAME = "CoqMakefile.conf"
COQ_HIDDEN_MAKEFILE_NAME = ".CoqMakefile.d"
LIA_CACHE_NAME = ".lia.cache"

COQ_BUILD_FILES = [COQ_PROJECT_NAME, COQ_MAKEFIE_NAME, 
                   COQ_CONF_NAME, COQ_HIDDEN_MAKEFILE_NAME, LIA_CACHE_NAME]


def clean_up(dir_loc: str) -> None:
    for build_file_name in COQ_BUILD_FILES:
        build_file_loc = os.path.join(dir_loc, build_file_name)
        if os.path.exists(build_file_loc):
            os.remove(build_file_loc)
    for subname in os.listdir(dir_loc):
        subdir_loc = os.path.join(dir_loc, subname)
        if os.path.isdir(subdir_loc):
            clean_up(subdir_loc)
        

COQFILE_CONTENTS = """\
-R theories CoqRepos
.
"""

def make_at_dir(dir_loc: str) -> None:
    coq_project_loc = os.path.join(dir_loc, COQ_PROJECT_NAME)
    with open(coq_project_loc, "w") as fout:
        fout.write(COQFILE_CONTENTS)
    os.chdir(dir_loc)
    p_create_makefile = subprocess.run(["coq_makefile", "-f", COQ_PROJECT_NAME, "-o", COQ_MAKEFIE_NAME])
    assert p_create_makefile.returncode == 0
    p_make_dir = subprocess.run(["make", "-f", COQ_MAKEFIE_NAME])
    if p_make_dir.returncode != 0:
        for subdir_name in os.listdir(dir_loc):
            subdir_loc = os.path.join(dir_loc, subdir_name)
            make_at_dir(subdir_loc)


def recurse_compile(coq_file_tree_loc: str) -> None:
    clean_up(coq_file_tree_loc)
    make_at_dir


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=("Try to compile as many coq projects in " 
                                                  "the given directory as possible."))
    parser.add_argument("coq_file_tree_loc", type=str, help="Hierarchy of coq files.")
    args = parser.parse_args(sys.argv[1:])
    recurse_compile(args.coq_file_tree_loc)



    
