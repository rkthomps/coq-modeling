from __future__ import annotations
from typing import Any
import sys, os
import shutil
import argparse
import traceback
import csv
import json
import ipdb
import multiprocessing as mp
import logging
from tqdm import tqdm

from dataclasses import dataclass

from util.util import LOGGER


from coqpyt.coq.base_file import CoqFile
from coqpyt.coq.proof_file import ProofFile
from coqpyt.coq.context import FileContext
from coqpyt.coq.structs import ProofTerm, Term



def get_context(
    context: list[Term], pm: PathManager 
) -> Any:
    res: list[Any] = []
    for term in context:
        res.append(
            {
                "text": term.text,
                "file_path": pm.translate_path(term.file_path),
                "module": term.module,
                "type": str(term.type),
                "line": term.ast.range.start.line,
            }
        )
    return res

def get_data_point_loc(project_name: str, valid_file: ValidFile, dp_dir) -> str:
    file_name = os.path.join(project_name, valid_file.relpath).replace("/", "-")
    return os.path.join(dp_dir, file_name)

def save_data_point(
    context: FileContext,
    proofs: list[ProofTerm],
    pm: PathManager,
    repos_dir: str,
    project_name: str,
    valid_file: ValidFile,
    dp_dir: str,
) -> None:
    if len(proofs) == 0:
        return

    file_folder = get_data_point_loc(project_name, valid_file, dp_dir)
    LOGGER.info(f"Saving to folder: {file_folder}")
    os.makedirs(file_folder, exist_ok=True)


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
                    "file_path": pm.translate_path(proof.file_path),
                    "module": proof.module,
                    "type": str(proof.type),
                    "line": proof.ast.range.start.line,
                    "context": get_context(
                        proof.context, pm 
                    ),
                },
                "step": {
                    "text": step.text,
                    "context": get_context(
                        step.context, pm 
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
                            next_step.context, pm 
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
                    "file": pm.translate_path(proofs[0].file_path),
                    "workspace": pm.translate_path(valid_file.full_workspace),
                    "repository": pm.translate_path(orig_project_loc),
                    "context": get_context(
                        list(context.terms.values()),
                        pm,
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

@dataclass
class PathManager:
    path_prefix_translations: dict[str, str]

    def list_prefixes(self) -> list[str]:
        return list(self.path_prefix_translations.keys())

    def translate_path(self, file: str) -> str:
        for orig_prefix, target_prefix in self.path_prefix_translations.items():
            if file.startswith(orig_prefix):
                orig_relpath = os.path.relpath(file, orig_prefix)
                return os.path.join(target_prefix, orig_relpath)
        raise ValueError(f"{file} does not match with any available prefixes {self.list_prefixes()}")



VALID_FILE_NAME = "valid_files.csv"


def could_have_proof(repos_dir: str, project_name: str, valid_file: ValidFile) -> bool:
    file_path = os.path.join(repos_dir, project_name, valid_file.relpath)
    with open(file_path, "r") as fin:
        contents = fin.read()
    # All the possible ways to name a proof
    if (
        "Theorem" in contents
        or "Lemma" in contents
        or "Fact" in contents
        or "Remark" in contents
        or "Corollary" in contents
        or "Proposition" in contents
        or "Property" in contents
    ):
        return True
    return False


def get_valid_files(repos_dir: str, project_name: str) -> list[ValidFile]:
    repo_loc = os.path.join(repos_dir, project_name)
    valid_files: list[ValidFile] = []
    with open(os.path.join(repo_loc, VALID_FILE_NAME), "r") as fin:
        csv_reader = csv.reader(fin)
        for row in csv_reader:
            relpath, full_workspace, version = row
            valid_files.append(ValidFile(relpath, full_workspace, version))
    return valid_files



def process_file(repos_dir: str, project_name: str, dp_dir: str, file: ValidFile, pm: PathManager) -> None:
    LOGGER.info(f"Processing {file.relpath}")
    if not could_have_proof(repos_dir, project_name, file):
        LOGGER.info(f"{file.relpath} could not possibly have proofs. Continuing.")
        return 
    file_folder = get_data_point_loc(project_name, file, dp_dir)
    if os.path.exists(file_folder):
        LOGGER.warning(f"{file_folder} exists. Continuing.")
        return

    with ProofFile(
        file.get_full_path(repos_dir, project_name),
        timeout=120,
        workspace=file.full_workspace,
    ) as proof_file:
        for _ in range(len(proof_file.steps)):
            proof_file.exec()
        context = proof_file.context
        proofs = proof_file.proofs

        # TODO: ADD ERROR HANDLING
        LOGGER.info(f"Saving {len(proofs)} proofs")
        save_data_point(
            context, proofs, pm, repos_dir, project_name, file, dp_dir
        )

def tolerant_process_file(repos_dir: str, project_name: str, dp_dir: str, file: ValidFile, pm: PathManager) -> None:
    try:
        process_file(repos_dir, project_name, dp_dir, file, pm)
    except:
        traceback.print_exc()
        file_folder = get_data_point_loc(project_name, file, dp_dir)
        if os.path.exists(file_folder):
            shutil.rmtree(file_folder)
        LOGGER.error(f"Trouble processing {file.relpath}")



def save_project_data_points(repos_dir: str, project_name: str, dp_dir: str, pm: PathManager) -> None:
    project_valid_files = get_valid_files(repos_dir, project_name)
    LOGGER.info(f"Found {len(project_valid_files)} valid files.")
    for valid_file in project_valid_files:
        tolerant_process_file(repos_dir, project_name, dp_dir, valid_file, pm)


_FILE_PROC_ARG = tuple[str, str, str, ValidFile, PathManager]
def get_project_multiprocessing_args(repos_dir: str, project_name: str, dp_dir: str, pm: PathManager) -> list[_FILE_PROC_ARG]:
    proc_args: list[_FILE_PROC_ARG] = []
    project_valid_files = get_valid_files(repos_dir, project_name)
    for valid_file in project_valid_files:
        proc_args.append((repos_dir, project_name, dp_dir, valid_file, pm))
    return proc_args
    

TRANSPLANT_REPOS_DIR = os.path.join("/coq-dataset", "repos")
TRANSPLANT_OPAM_DIR = os.path.join("/root", ".opam")


if __name__ == "__main__":
    parser = argparse.ArgumentParser("Get Data Points for a given project")
    parser.add_argument("repos_dir", help="Location where repositories are downloaded.")
    parser.add_argument("opam_dir", help="Location of local opam switch.")
    parser.add_argument("project_name", help="Project for which you want data points.")
    parser.add_argument("dp_dir", help="Location to save the data point files.")
    parser.add_argument("--n_procs", "-n", type=int, help="Number of processes to use for the project.")

    args = parser.parse_args(sys.argv[1:])
    abs_repos = os.path.abspath(args.repos_dir)
    abs_opam = os.path.abspath(args.opam_dir)
    pm = PathManager({
        abs_repos: TRANSPLANT_REPOS_DIR,
        abs_opam: TRANSPLANT_OPAM_DIR,
    })

    if args.n_procs is None:
        LOGGER.info("Processing with a single process.")
        save_project_data_points(abs_repos, args.project_name, args.dp_dir, pm)
    else:
        LOGGER.info(f"Processing with a {args.n_procs} processes.")
        file_args = get_project_multiprocessing_args(abs_repos, args.project_name, args.dp_dir, pm)
        with mp.Pool(args.n_procs) as pool:
            pool.starmap(tolerant_process_file, file_args)

