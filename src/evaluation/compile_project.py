from typing import Any
import sys, os
import argparse
import logging
import json

from data_management.splits import REPOS_NAME
from util import util

_logger = util.get_basic_logger(__name__, logging.WARN)

COQ_CRAWLER_LOC = "coq-crawler"
if not COQ_CRAWLER_LOC in sys.path:
    sys.path.insert(0, COQ_CRAWLER_LOC)

COQ_PYT_LOC = os.path.join("coqpyt", "coqpyt")
if not COQ_PYT_LOC in sys.path:
    sys.path.insert(0, COQ_PYT_LOC)

from project import Project, ValidFile


def valid_file_to_json(valid_file: ValidFile, raw_data_loc: str) -> Any:
    abs_raw_data_loc = os.path.abspath(raw_data_loc)
    assert valid_file.workspace.startswith(abs_raw_data_loc)
    workspace_rel_loc = os.path.relpath(valid_file.workspace, abs_raw_data_loc)
    return {"workspace": workspace_rel_loc}


def valid_file_workspace(json_data: Any) -> str:
    workspace = json_data["workspace"]
    assert isinstance(workspace, str)
    return workspace


def dot_v_to_json(filename: str) -> str:
    if not filename.endswith(".v"):
        raise ValueError(f"{filename} does not end with '.v'.")
    return filename.rstrip(".v") + ".json"


def compile_project(raw_data_loc: str, project_name: str, build_save_loc: str) -> None:
    project_loc = os.path.join(raw_data_loc, REPOS_NAME, project_name)
    _logger.debug(f"Compiling: {project_loc}")
    project_save_loc = os.path.join(build_save_loc, REPOS_NAME, project_name)
    os.makedirs(project_save_loc, exist_ok=True)
    project_files = os.listdir(project_loc)
    if len(project_files) == 0:
        _logger.warning(f"Project {project_loc} has no files.")
        return
    random_file = project_files[0]
    # Have to pass in a file of the project -- not the project itself.
    project_path = os.path.abspath(os.path.join(project_loc, random_file))
    project = Project(project_path, debug=True)

    for valid_file in project.valid_files:
        valid_file_json = valid_file_to_json(valid_file, raw_data_loc)
        relpath_as_json = dot_v_to_json(valid_file.relpath)
        file_save_loc = os.path.join(project_save_loc, relpath_as_json)
        os.makedirs(os.path.dirname(file_save_loc), exist_ok=True)
        _logger.debug(f"File save loc: {file_save_loc}")
        with open(file_save_loc, "w") as fout:
            fout.write(json.dumps(valid_file_json, indent=2))


if __name__ == "__main__":
    sys.setrecursionlimit(1500)
    parser = argparse.ArgumentParser(
        description="Compile a single project and save its metadata."
    )
    parser.add_argument("raw_data_loc", help="Path to raw dataset")
    parser.add_argument("project_name", help="Name of the repository")
    parser.add_argument("build_save_loc", help="Directory to save building metadata.")
    args = parser.parse_args(sys.argv[1:])
    compile_project(args.raw_data_loc, args.project_name, args.build_save_loc)
    _logger.debug("Done.")
    os._exit(os.EX_OK)
