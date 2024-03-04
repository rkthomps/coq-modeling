from __future__ import annotations
from typing import Any
import sys, os
import argparse
import traceback
import csv
import json
import ipdb

from dataclasses import dataclass

from util.util import get_basic_logger

from coqpyt.coq.base_file import CoqFile
from coqpyt.coq.proof_file import ProofFile
from coqpyt.coq.context import FileContext
from coqpyt.coq.structs import ProofTerm

_logger = get_basic_logger(__name__)


def get_proof_steps(
    repos_dir: str, project_name: str, file: ValidFile
) -> tuple[FileContext, list[ProofTerm]]:
    """Copied from coqpyt-crawler. ProofFile might throw an error."""
    with ProofFile(
        file.get_full_path(repos_dir, project_name),
        timeout=60,
        workspace=file.full_workspace,
    ) as proof_file:
        proof_file.run()
        context = proof_file.context
        proofs = proof_file.proofs

    # Decrease storage required
    for term in context.terms.values():
        term.ast.span = None
    for proof in proofs:
        for step in proof.steps:
            step.ast.span = None
            for term in step.context:
                term.ast.span = None
    return context, proofs


def proc_file_path(
    file_path: str, orig_repos_dir: str, transplant_repos_dir: str
) -> str:
    assert file_path.startswith(orig_repos_dir)
    orig_relpath = os.path.relpath(file_path, orig_repos_dir)
    return os.path.join(transplant_repos_dir, orig_relpath)


def get_context(
    context: list[ProofTerm], orig_repos_dir: str, transplant_repos_dir: str
) -> Any:
    res: list[Any] = []
    for term in context:
        res.append(
            {
                "text": term.text,
                "file_path": proc_file_path(
                    term.file_path, orig_repos_dir, transplant_repos_dir
                ),
                "module": term.module,
                "type": str(term.type),
                "line": term.ast.range.start.line,
            }
        )
    return res


def save_data_point(
    context: FileContext,
    proofs: list[ProofTerm],
    repos_dir: str,
    transplant_repos_dir: str,  # So that the prefix aligns with previously created ones
    project_name: str,
    valid_file: ValidFile,
    dp_dir: str,
) -> None:
    if len(proofs) == 0:
        return

    file_folder = os.path.join(
        dp_dir, project_name, valid_file.relpath.replace("/", "-")
    )
    _logger.info(f"Saving to folder: {file_folder}")

    if not os.path.exists(file_folder):
        os.mkdir(file_folder)
    open(os.path.join(file_folder, "steps.jsonl"), "w").close()

    for proof in proofs:
        # Remove Admitted and Aborted proofs
        if len(proof.steps) == 0 or proof.steps[-1].text.strip().endswith(
            ("Admitted.", "Aborted.")
        ):
            continue
        for i, step in enumerate(proof.steps):
            goals = list(map(lambda goal: repr(goal), step.goals.goals.goals))
            data_point = {
                "term": {
                    "text": proof.text,
                    "file_path": proc_file_path(
                        proof.file_path, repos_dir, transplant_repos_dir
                    ),
                    "module": proof.module,
                    "type": str(proof.type),
                    "line": proof.ast.range.start.line,
                    "context": get_context(
                        proof.context, repos_dir, transplant_repos_dir
                    ),
                },
                "step": {
                    "text": step.text,
                    "context": get_context(
                        step.context, repos_dir, transplant_repos_dir
                    ),
                },
                "n_step": i + 1,
                "goals": goals,
                "next_steps": [],
            }
            for next_step in proof.steps[i + 1 :]:
                data_point["next_steps"].append(
                    {
                        "text": next_step.text,
                        "context": get_context(
                            next_step.context, repos_dir, transplant_repos_dir
                        ),
                    }
                )

            with open(os.path.join(file_folder, "steps.jsonl"), "a") as f:
                f.write(json.dumps(data_point) + "\n")

        orig_project_loc = os.path.join(repos_dir, project_name)
        with open(os.path.join(file_folder, "file_context.jsonl"), "w") as f:
            f.write(
                json.dumps(
                    {
                        "file": os.path.abspath(
                            proc_file_path(
                                proofs[0].file_path, repos_dir, transplant_repos_dir
                            )
                        ),
                        "workspace": proc_file_path(
                            valid_file.full_workspace, repos_dir, transplant_repos_dir
                        ),
                        "repository": proc_file_path(
                            orig_project_loc, repos_dir, transplant_repos_dir
                        ),
                        "context": get_context(
                            list(context.terms.values()),
                            repos_dir,
                            transplant_repos_dir,
                        ),
                    }
                )
            )


@dataclass
class ValidFile:
    relpath: str
    full_workspace: str
    version: str

    def get_full_path(self, repos_dir: str, project_name: str) -> str:
        return os.path.join(repos_dir, project_name, self.relpath)


VALID_FILE_NAME = "valid_files.csv"


def could_have_proof(repos_dir: str, project_name: str, valid_file: ValidFile) -> bool:
    file_path = os.path.join(repos_dir, project_name, valid_file.relpath)
    with open(file_path, "r") as fin:
        contents = fin.read()

    if (
        "Theorem" in contents
        or "Lemma" in contents
        # TODO
    ):
        pass


def get_valid_files(repos_dir: str, project_name: str) -> list[ValidFile]:
    repo_loc = os.path.join(repos_dir, project_name)
    valid_files: list[ValidFile] = []
    with open(os.path.join(repo_loc, VALID_FILE_NAME), "r") as fin:
        csv_reader = csv.reader(fin)
        for row in csv_reader:
            relpath, full_workspace, version = row
            valid_files.append(ValidFile(relpath, full_workspace, version))
    return valid_files


TRANSPLANT_DIR = os.path.join("/coq-dataset", "repos")


def save_project_data_points(repos_dir: str, project_name: str, dp_dir: str) -> None:
    project_valid_files = get_valid_files(repos_dir, project_name)
    _logger.info(f"Found {len(project_valid_files)} valid files.")
    for valid_file in project_valid_files:
        _logger.info(f"Processing {valid_file.relpath}")
        context, proofs = get_proof_steps(repos_dir, project_name, valid_file)
        # TODO: ADD ERROR HANDLING
        _logger.info(f"Saving {len(proofs)} proofs")
        save_data_point(
            context, proofs, repos_dir, TRANSPLANT_DIR, project_name, valid_file, dp_dir
        )


if __name__ == "__main__":
    parser = argparse.ArgumentParser("Get Data Points for a given project")
    parser.add_argument("repos_dir", help="Location where repositories are downloaded.")
    parser.add_argument("project_name", help="Project for which you want data points.")
    parser.add_argument("dp_dir", help="Location to save the data point files.")

    args = parser.parse_args(sys.argv[1:])
    abs_repos = os.path.abspath(args.repos_dir)
    save_project_data_points(abs_repos, args.project_name, args.dp_dir)
