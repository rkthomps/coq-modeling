from typing import Optional

import pexpect
import os
import re
import json
import time
from pathlib import Path
import logging
import argparse

from dataclasses import dataclass

from coqstoq import get_theorem, get_theorem_list, Split
from coqstoq.eval_thms import EvalTheorem, get_file_hash
from coqstoq.check import Result, EvalResults

from util.file_queue import FileQueue, EmptyFileQueueError


@dataclass
class CoqHammerEvalConf:
    coqstoq_loc: Path
    split: Split
    save_loc: Path


class CoqTop:
    def __init__(
        self,
        file: str,
        timeout: int = 10,
        workdir: str | None = None,
        options: str = "",
    ):
        self.process = pexpect.spawn(
            f"coqtop -load-vernac-source {file} {options}",
            encoding="utf-8",
            timeout=timeout,
            cwd=workdir,
        )
        try:
            self.process.expect("([a-zA-z1-9_][^\n]*?) < ")
        except Exception as e:
            self.process.kill(9)
            raise e

    def run(self, command: str, expect: str = "([a-zA-z1-9_][^\n]*?) < "):
        self.process.write(command + "\n")
        self.process.expect(expect)
        return self.process.before

    def kill(self):
        self.process.kill(9)


def get_file_prefix(thm: EvalTheorem, coqstoq_loc: Path) -> str:
    thm_path = coqstoq_loc / thm.project.workspace / thm.path
    file_text = thm_path.read_text()
    file_lines = file_text.split("\n")
    file_prefix_lines = file_lines[: thm.theorem_end_pos.line + 1].copy()
    file_prefix_lines[-1] = file_prefix_lines[-1][: thm.theorem_end_pos.column]
    file_prefix = "\n".join(file_prefix_lines)
    print("\n".join(file_prefix_lines[(-10):]))
    return file_prefix


def get_temp_save_loc(thm: EvalTheorem, coqstoq_loc: Path) -> Path:
    path = coqstoq_loc / thm.project.workspace / thm.path
    save_path = (
        path.parent
        / f"{thm.path.stem}_coqhammer_eval_{thm.theorem_start_pos.line}_{thm.theorem_start_pos.column}.v"
    )
    assert not save_path.exists()
    return save_path


def mk_eval_file(thm: EvalTheorem, coqstoq_loc: Path) -> Path:
    thm_path = coqstoq_loc / thm.project.workspace / thm.path
    assert thm_path.exists()
    assert get_file_hash(thm_path) == thm.hash
    file_prefix = get_file_prefix(thm, coqstoq_loc)
    save_path = get_temp_save_loc(thm, coqstoq_loc)
    with save_path.open("w") as fout:
        fout.write(file_prefix)
    return save_path


def test_theorem(thm: EvalTheorem, coqstoq_loc: Path, timeout: int) -> Optional[Result]:
    thm_path = coqstoq_loc / thm.project.workspace / thm.path
    thm_workspace = coqstoq_loc / thm.project.workspace
    options = " ".join(thm.project.compile_args)
    eval_file = mk_eval_file(thm, coqstoq_loc)

    # Complie file
    try:
        coq_top = CoqTop(
            str(eval_file.resolve()),
            timeout=timeout + 60,
            workdir=str(thm_workspace.resolve()),
            options=options,
        )
    except Exception as e:
        logging.warning(
            f"Failed to compile {thm.path} in workspace {thm_workspace}: {e}"
        )
        os.remove(eval_file)
        return None

    # Synthesize Proof
    start_time = time.time()
    try:
        print("Setting hammer limit.")
        coq_top.run(f"Set Hammer ATPLimit {timeout}.")
        print("Running hammer.")
        stdout = coq_top.run(
            "all: hammer.",
            expect="(No more goals\.)|(Hammer failed: ATPs failed to find a proof\.)",
        )
        stdout += coq_top.process.after
        coq_top.process.expect("([a-zA-z1-9_][^\n]*?) < ")
        stdout += coq_top.process.before
        if "Hammer failed: ATPs failed to find a proof." in stdout:
            print("PROOF FAILED")
            return Result(thm, None, time.time() - start_time)
        elif "No more goals." in stdout:
            print("PROOF SUCCEEDED")
            return Result(thm, "all: hammer.", time.time() - start_time)
        else:
            print("UNKNOWN PROOF STATUS")
            return None

    except pexpect.exceptions.TIMEOUT:
        return None

    except pexpect.exceptions.EOF:
        return None

    finally:
        coq_top.kill()
        os.remove(eval_file)


def get_coqstoq_split(choice: str) -> Split:
    match choice:
        case "val":
            return Split.VAL
        case "test":
            return Split.TEST
        case "cutoff":
            return Split.CUTOFF
        case _:
            raise ValueError(f"Invalid choice: {choice}")


def get_save_loc(eval_thm: EvalTheorem, save_loc: Path) -> Path:
    return (
        save_loc
        / eval_thm.project.workspace.name
        / eval_thm.path
        / f"{eval_thm.theorem_start_pos.line}-{eval_thm.theorem_start_pos.column}.json"
    )


def run_single(args: argparse.Namespace):
    coqstoq_loc = Path(args.coqstoq_loc)
    coqstoq_split = get_coqstoq_split(args.split)

    thms = get_theorem_list(coqstoq_split, coqstoq_loc)
    thm = thms[args.thm_idx]

    result = test_theorem(thm, coqstoq_loc, args.timeout)
    print(f"Would save to: ", get_save_loc(thm, Path("save-loc")))
    print(result)


def run_slurm(args: argparse.Namespace):
    coqstoq_loc = Path(args.coqstoq_loc)
    save_loc = Path(args.save_loc)
    queue_loc = Path(args.queue_loc)

    assert coqstoq_loc.exists()
    assert queue_loc.exists()

    while True:
        q = FileQueue[EvalTheorem](queue_loc)
        try:
            thm = q.get()
        except EmptyFileQueueError:
            break

        result_save_loc = get_save_loc(thm, save_loc)
        print("Running ", result_save_loc)
        result = test_theorem(thm, coqstoq_loc, args.timeout)
        if result is not None:
            os.makedirs(result_save_loc.parent, exist_ok=True)
            with result_save_loc.open("w") as fout:
                json.dump(result.to_json(), fout, indent=2)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="subparser_name", required=True)
    single_parser = subparsers.add_parser("single", help="Run a single theorem")
    single_parser.add_argument("--coqstoq_loc", type=str, required=True)
    single_parser.add_argument("--split", type=str, required=True)
    single_parser.add_argument("--thm_idx", type=int, required=True)
    single_parser.add_argument("--timeout", type=int, default=600)

    slurm_parser = subparsers.add_parser("slurm", help="Run as slurm worker")
    slurm_parser.add_argument("--coqstoq_loc", type=str, required=True)
    slurm_parser.add_argument("--save_loc", type=str, required=True)
    slurm_parser.add_argument("--queue_loc", type=str, required=True)
    slurm_parser.add_argument("--timeout", type=int, default=600)

    args = parser.parse_args()

    if args.subparser_name == "single":
        run_single(args)
    elif args.subparser_name == "slurm":
        run_slurm(args)
    else:
        raise ValueError(f"Unknown subparser: {args.subparser_name}")
