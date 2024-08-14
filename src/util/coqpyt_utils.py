from typing import Any

from coqpyt.coq.structs import GoalAnswer, Term
from coqpyt.coq.lsp.structs import Goal
from coqpyt.coq.base_file import CoqFile
from coqpyt.coq.proof_file import ProofFile

from data_management.dataset_file import FileContext
from data_management.sentence_db import SentenceDB

import ipdb


def get_all_goals(goal_answer: GoalAnswer) -> list[Goal]:
    assert goal_answer.goals is not None
    collapsed_stack: list[Goal] = []
    for stack_goals1, stack_goals2 in goal_answer.goals.stack:
        collapsed_stack.extend(stack_goals1)
        collapsed_stack.extend(stack_goals2)
    return goal_answer.goals.goals + collapsed_stack + goal_answer.goals.shelf


def go_through_point(coq_file: CoqFile, point: int) -> None:
    while coq_file.steps_taken < point + 1:
        coq_file.exec(1)
    while point + 1 < coq_file.steps_taken:
        coq_file.exec(-1)


def go_to_point(coq_file: CoqFile, point: int) -> None:
    while coq_file.steps_taken < point:
        coq_file.exec(1)
    while point < coq_file.steps_taken:
        coq_file.exec(-1)


def proc_file_path(file_path: str) -> str:
    if file_path.startswith("/home"):
        return "/".join(file_path.split("/")[3:])
    return file_path


def get_context(context: list[Term]) -> list[dict[str, Any]]:
    res: list[dict[str, Any]] = []
    for term in context:
        res.append(
            {
                "text": term.text,
                "file_path": proc_file_path(term.file_path),
                "module": term.module,
                "type": str(term.type),
                "line": term.ast.range.start.line,
            }
        )
    return res


def get_file_context(proof_file: ProofFile, sentence_db: SentenceDB) -> FileContext:
    last_proof = proof_file.proofs[-1]
    context_list = list(proof_file.context.terms.values())
    context_data = get_context(context_list)
    file_context_data = {
        "file": proc_file_path(last_proof.file_path),
        "workspace": proc_file_path(last_proof.file_path),
        "repository": "junkrepo",
        "context": context_data,
    }
    file_context = FileContext.from_verbose_json(file_context_data, sentence_db)
    return file_context
