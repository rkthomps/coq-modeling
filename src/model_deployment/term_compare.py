from __future__ import annotations
from typing import Any

from coqpyt.coq.base_file import CoqFile, GoalAnswer
from data_management.splits import DataSplit, FileInfo


"""

I want to get the proof for the current goal. 
Is it true that the current goal is solved when  

len(all goals) = 1 - len(current goal) ? 

"""

from data_management.splits import FileInfo


def simplify_ast1(coq_ast: Any) -> Any:
    match coq_ast:
        case {"v": rest, "loc": _}:
            return simplify_ast1(rest)
        case dict():
            return {simplify_ast(k): simplify_ast(v) for k, v in coq_ast.items()}
        case list():
            return [simplify_ast(i) for i in coq_ast]
        case other:
            return other


def simplify_ast2(coq_ast: Any) -> Any:
    match coq_ast:
        case ["CRef", ["Ser_Qualid", ["DirPath", []], ["Id", id]], None]:
            return ["Id", id]
        case dict():
            return {simplify_ast2(k): simplify_ast2(v) for k, v in coq_ast.items()}
        case list():
            return [simplify_ast2(i) for i in coq_ast]
        case other:
            return other


def simplify_ast(coq_ast: Any) -> Any:
    simp = simplify_ast1(coq_ast)
    simp = simplify_ast2(simp)
    return simp


def get_all_normal_goals_and_proofs(file_info: FileInfo):
    pass
