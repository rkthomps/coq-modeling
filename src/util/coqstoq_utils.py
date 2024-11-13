from coqstoq import Split
from coqstoq.eval_thms import EvalTheorem
from pathlib import Path


def str2split(s: str) -> Split:
    match s:
        case "cutoff":
            return Split.CUTOFF
        case "test":
            return Split.TEST
        case "val":
            return Split.VAL
        case _:
            raise ValueError(f"Invalid choice: {s}")


def split2str(s: Split) -> str:
    match s:
        case Split.CUTOFF:
            return "cutoff"
        case Split.TEST:
            return "test"
        case Split.VAL:
            return "val"


def get_file_loc(thm: EvalTheorem, coqstoq_loc: Path) -> Path:
    return coqstoq_loc / thm.project.workspace / thm.path


def get_workspace_loc(thm: EvalTheorem, coqstoq_loc: Path) -> Path:
    return coqstoq_loc / thm.project.workspace
