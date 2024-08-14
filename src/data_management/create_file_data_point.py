import os
from typing import Any, Optional

import argparse
import ipdb
import subprocess

import logging

from dataclasses import dataclass
from pathlib import Path
from coqpyt.coq.base_file import CoqFile
from coqpyt.coq.proof_file import ProofFile

from coqpyt.coq.proof_file import ProofFile
from coqpyt.coq.structs import ProofTerm, Term

from data_management.dataset_file import DatasetFile, FocusedStep, FileContext, Proof
from data_management.sentence_db import SentenceDB

from util.util import get_basic_logger

_logger = get_basic_logger(__name__)


def get_context(
    context: list[Term],
    workspace_loc: Path,
    translate: bool,
    switch_loc: Optional[Path],
) -> Any:
    res: list[Any] = []
    for term in context:
        res.append(
            {
                "text": term.text,
                "file_path": translate_path(
                    Path(term.file_path), workspace_loc, translate, switch_loc
                ),
                "module": term.module,
                "type": str(term.type),
                "line": term.ast.range.start.line,
            }
        )
    return res


def proof_file_to_data_point(
    proof_file: ProofFile,
    sentence_db: SentenceDB,
    workspace: Path,
    repository: Path,
    add_to_dataset: bool,
    switch_loc: Optional[Path],
) -> DatasetFile:
    proof_file_steps: list[Any] = []
    proof_file_path: Optional[Path] = None
    for proof in proof_file.proofs:
        proof_file_path = Path(proof.file_path)
        if len(proof.steps) == 0 or proof.steps[-1].text.strip().endswith(
            ("Admitted.", "Aborted.")
        ):
            continue
        for i, step in enumerate(proof.steps):
            goals = list(map(lambda goal: repr(goal), step.goals.goals.goals))
            data_point = {
                "term": {
                    "text": proof.text,
                    "file_path": translate_path(
                        proof_file_path, workspace, add_to_dataset, switch_loc
                    ),
                    "module": proof.module,
                    "type": str(proof.type),
                    "line": proof.ast.range.start.line,
                    "context": get_context(
                        proof.context, workspace_loc, add_to_dataset, switch_loc
                    ),
                },
                "step": {
                    "text": step.text,
                    "context": get_context(
                        proof.context, workspace_loc, add_to_dataset, switch_loc
                    ),
                },
                "n_step": i + 1,
                "goals": goals,
            }
            proof_file_steps.append(data_point)

    if len(proof_file.proofs) == 0:
        raise ValueError(f"No proofs.")

    proof_steps = [
        FocusedStep.from_json(step, sentence_db) for step in proof_file_steps
    ]
    proofs = DatasetFile.proofs_from_steps(proof_steps)

    assert proof_file_path is not None
    verbose_file_context_json = {
        # "file": pm.translate_path(proof_file.proofs[0].file_path),
        # "workspace": pm.translate_path(valid_file.full_workspace),
        # "repository": pm.translate_path(orig_project_loc),
        "file": translate_path(
            Path(proof_file_path), workspace, add_to_dataset, switch_loc
        ),
        "workspace": str(workspace.resolve()),
        "repository": str(repository.resolve()),
        "context": get_context(
            list(proof_file.context.terms.values()),
            workspace_loc,
            add_to_dataset,
            switch_loc,
        ),
    }
    file_context = FileContext.from_verbose_json(verbose_file_context_json, sentence_db)
    return DatasetFile(file_context, proofs)


def get_data_point(
    file_loc: Path,
    workspace_loc: Path,
    sentence_db: SentenceDB,
    add_to_dataset: bool,
    switch_loc: Optional[Path],
    compile_timeout: int = 600,
) -> DatasetFile:
    _logger.info("Compiling coq file...")
    with CoqFile(
        str(file_loc.resolve()),
        workspace=str(workspace_loc.resolve()),
        timeout=compile_timeout,
    ) as coq_file:
        if not coq_file.is_valid:
            raise ValueError(f"Could not compile coq file: {coq_file}")

    _logger.info("Generating proof file...")
    with ProofFile(
        str(file_loc.resolve()),
        workspace=str(workspace_loc.resolve()),
        timeout=compile_timeout,
    ) as proof_file:
        proof_file.run()
        return proof_file_to_data_point(
            proof_file,
            sentence_db,
            workspace_loc,
            workspace_loc,
            add_to_dataset,
            switch_loc,
        )


DATASET_PREFIX = Path("/coq-dataset/repos")
DATASET_OPAM_PREFIX = "/root/.opam/default"
COQ_BIN_PATH = Path("bin/coqc")


def to_dataset_format(path: Path, workspace: Path, switch_path: Path) -> Path:
    if path.is_relative_to(workspace.resolve()):
        return (DATASET_PREFIX / workspace.name) / path.relative_to(workspace.resolve())
    elif path.is_relative_to(switch_path.resolve()):
        return DATASET_OPAM_PREFIX / path.relative_to(switch_path.resolve())
    else:
        raise ValueError(f"Path {path} is not relative to {workspace} or {switch_path}")


def translate_path(
    path: Path, workspace: Path, translate: bool, switch_path: Optional[Path]
) -> str:
    if not translate:
        return str(path)
    assert switch_path is not None
    return str(to_dataset_format(path, workspace, switch_path))


if __name__ == "__main__":
    parser = argparse.ArgumentParser("Create data points file for given file.")
    parser.add_argument("--file_loc", type=str, help="Location of the file.")
    parser.add_argument(
        "--workspace_loc", type=str, help="Location of the file's workspace"
    )
    parser.add_argument("--sentence_db_loc", help="Location of the sentence_db")
    parser.add_argument(
        "--save_loc", type=str, help="Location to save the data point file."
    )
    parser.add_argument(
        "--add_to_dataset",
        action="store_true",
        help="Whether to add the data point to a ML dataset.",
        default=False,
    )

    args = parser.parse_args()

    file_loc = Path(args.file_loc)
    workspace_loc = Path(args.workspace_loc)
    sentence_db_loc = Path(args.sentence_db_loc)
    add_to_dataset = args.add_to_dataset
    save_loc = Path(args.save_loc)

    assert file_loc.exists()
    assert workspace_loc.exists()
    assert not save_loc.exists()

    sentence_db = SentenceDB.load(sentence_db_loc)

    if add_to_dataset:
        opam_loc = Path(
            subprocess.run("which coqc", shell=True, capture_output=True)
            .stdout.decode()
            .strip()
        ).resolve()
        assert (opam_loc.parents[1] / COQ_BIN_PATH).exists()
        switch_loc = opam_loc.parents[1]
    else:
        switch_loc = None

    print("WORKSPACE", workspace_loc.resolve())

    dp = get_data_point(
        file_loc.resolve(),
        workspace_loc.resolve(),
        sentence_db,
        add_to_dataset,
        switch_loc,
    )
    ipdb.set_trace()

    # if save_loc.exists():
    #     raise FileExistsError(f"File {save_loc} already exists.")
