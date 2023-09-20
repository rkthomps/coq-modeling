

import sys, os
import argparse
from impose_file_hierarchy import NEW_ROOT_NAME 

COQ_PROJECT_NAME = "_CoqProject"

COQ_PROJECT_PREFIX = "-R theories CoqRepos"

def get_project_dirs(tree_parent_loc: str) -> list[str]:
    assert NEW_ROOT_NAME in os.listdir(tree_parent_loc)
    repo_paths = []
    root_loc = os.path.join(tree_parent_loc, NEW_ROOT_NAME)
    for repo in os.listdir(root_loc):
        repo_path = os.path.join(NEW_ROOT_NAME, repo)
        repo_paths.append(repo_path)
    return repo_paths


def compile_corpus(tree_parent_loc: str) -> None:
    coq_project_loc = os.path.join(tree_parent_loc, COQ_PROJECT_NAME)
    if os.path.exists(coq_project_loc):
        os.remove(coq_project_loc)
    project_dirs = get_project_dirs(tree_parent_loc)
    dirs_as_str = "\n".join(project_dirs)
    coq_project_contents = f"{COQ_PROJECT_PREFIX}\n{dirs_as_str}"
    with open(coq_project_loc, "w") as fout:
        fout.write(coq_project_contents)


if __name__ == "__main__":
    parser = argparse.ArgumentParser("Compile a set of coq repos.")
    parser.add_argument("tree_parent_loc", help="Location of the output directory from impose_file_hierarchy.py.")
    args = parser.parse_args(sys.argv[1:])
    compile_corpus(args.tree_parent_loc)


