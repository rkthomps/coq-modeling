import os
import json
import argparse
from pathlib import Path
from data_management.splits import DataSplit, Split
from coqpyt.coq.base_file import CoqFile
from util.util import get_basic_logger

_logger = get_basic_logger(__name__)


TESTING_REPOS = [
    "AbsInt-CompCert",
    "coq-community-coq-ext-lib",
    "coq-community-fourcolor",
    "coq-community-math-classes",
    "coq-community-reglang",
    "coq-community-buchberger",
    "coq-community-hoare-tut",
    "coq-community-zorns-lemma",
    "coq-community-huffman",
    "thery-PolTac",
    "coq-community-dblib",
    "coq-contribs-zfc",
]


def find_missing_files(
    data_split: DataSplit, project_dir: Path, data_loc: Path
) -> list[Path]:
    split_files = set([data_loc / f.file for f in data_split.get_file_list(Split.TEST)])
    project_missing_files: list[Path] = []
    for root, dirs, files in os.walk(project_dir):
        for file in files:
            file_path = Path(root) / file
            if file.endswith(".v") and file_path not in split_files:
                project_missing_files.append(file_path)
    return project_missing_files


def find_compiling_missing_files(
    workspace_loc: Path, missing_files: list[Path]
) -> list[Path]:
    compiling_files: list[Path] = []
    for file in missing_files:
        try:
            with CoqFile(
                str(file.resolve()), workspace=str(workspace_loc.resolve())
            ) as coq_file:
                coq_file.run()
                if coq_file.is_valid:
                    compiling_files.append(file)
                    _logger.info(f"Checked {file}... OK!")
                else:
                    _logger.info(f"Checked {file}... Not OK.")
        except Exception as e:
            _logger.error(f"Error checking {file}: {e}")
    return compiling_files


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        "Verify that there are no missing files in given split's testing set. If there are, save them."
    )
    parser.add_argument("--split_loc", type=str, required=True)
    parser.add_argument("--data_loc", type=str, required=True)
    parser.add_argument("--repos_dir", type=str, required=True)

    args = parser.parse_args()
    split_loc = Path(args.split_loc)
    repos_dir = Path(args.repos_dir)
    assert split_loc.exists()
    assert repos_dir.exists()

    data_split = DataSplit.load(split_loc)

    missing_compiled_files: list[Path] = []
    for test_repo in TESTING_REPOS:
        project_dir = repos_dir / test_repo
        assert (repos_dir / test_repo).exists()
        proj_missing_files = find_missing_files(
            data_split, project_dir, data_loc=Path(args.data_loc)
        )
        proj_missing_compiled_files = find_compiling_missing_files(
            project_dir, proj_missing_files
        )
        missing_compiled_files.extend(proj_missing_compiled_files)

    with open("missing_files.json", "w") as fout:
        missing_file_strs = [str(f) for f in missing_compiled_files]
        json.dump(missing_file_strs, fout, indent=2)
