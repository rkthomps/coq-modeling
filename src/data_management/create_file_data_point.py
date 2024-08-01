import os
from typing import Any
import argparse

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
        raise ValueError(
            f"{file} does not match with any available prefixes {self.list_prefixes()}"
        )


def get_context(context: list[Term], pm: PathManager) -> Any:
    res: list[Any] = []
    for term in context:
        res.append(
            {
                "text": term.text,
                # "file_path": pm.translate_path(term.file_path),
                "file_path": term.file_path,
                "module": term.module,
                "type": str(term.type),
                "line": term.ast.range.start.line,
            }
        )
    return res


def proof_file_to_data_point(
    proof_file: ProofFile,
    sentence_db: SentenceDB,
    pm: PathManager,
    workspace: Path,
    repository: Path,
) -> DatasetFile:
    proof_file_steps: list[Any] = []
    for proof in proof_file.proofs:
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
                    "context": get_context(proof.context, pm),
                },
                "step": {
                    "text": step.text,
                    "context": get_context(step.context, pm),
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

    verbose_file_context_json = {
        # "file": pm.translate_path(proof_file.proofs[0].file_path),
        # "workspace": pm.translate_path(valid_file.full_workspace),
        # "repository": pm.translate_path(orig_project_loc),
        "file": proof_file.proofs[0].file_path,
        "workspace": str(workspace.resolve()),
        "repository": str(repository.resolve()),
        "context": get_context(
            list(proof_file.context.terms.values()),
            pm,
        ),
    }
    file_context = FileContext.from_verbose_json(verbose_file_context_json, sentence_db)
    return DatasetFile(file_context, proofs)


def get_data_point(
    file_loc: Path,
    workspace_loc: Path,
    sentence_db: SentenceDB,
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
            proof_file, sentence_db, PathManager({}), workspace_loc, workspace_loc
        )


if __name__ == "__main__":
    parser = argparse.ArgumentParser("Create data points file for given file.")
    parser.add_argument("file_loc", type=str, help="Location of the file.")
    parser.add_argument(
        "workspace_loc", type=str, help="Location of the file's workspace"
    )
    parser.add_argument("sentence_db_loc", help="Location of the sentence_db")
    # parser.add_argument(
    #     "save_loc", type=str, help="Location to save the data point file."
    # )

    args = parser.parse_args()

    file_loc = Path(args.file_loc)
    workspace_loc = Path(args.workspace_loc)
    sentence_db_loc = Path(args.sentence_db_loc)
    # save_loc = Path(args.save_loc)

    assert file_loc.exists()
    assert workspace_loc.exists()

    sentence_db = SentenceDB.load(sentence_db_loc)

    get_data_point(file_loc, workspace_loc, sentence_db)

    # if save_loc.exists():
    #     raise FileExistsError(f"File {save_loc} already exists.")
