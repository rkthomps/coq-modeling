from __future__ import annotations
from typing import Any

import os
import yaml
import shutil
import subprocess
from pathlib import Path
import argparse

from util.slurm import slurm_conf_from_yaml, get_queue_slurm_loc, run_local
from util.file_queue import FileQueue
from util.util import set_rango_logger
import subprocess

from tqdm import tqdm
from coqstoq import get_theorem_list, Split
from coqstoq.eval_thms import EvalTheorem

import logging


WORKER_LOC = Path("scripts/eval_coqhammer.py")


def fill_queue(
    queue_loc: Path, coqstoq_split: Split, coqstoq_loc: Path, save_loc: Path
) -> None:
    q: FileQueue[EvalTheorem] = FileQueue(queue_loc)
    q.initialize()
    thms = get_theorem_list(coqstoq_split, coqstoq_loc)
    num_added = 0
    for t in tqdm(thms):
        if get_save_loc(t, save_loc).exists():
            continue
        q.put(t)
        num_added += 1
    print(f"Added {num_added} to queue.")


# Copied this from eval_tactician.py
def get_save_loc(eval_thm: EvalTheorem, save_loc: Path) -> Path:
    return (
        save_loc
        / eval_thm.project.workspace.name
        / eval_thm.path
        / f"{eval_thm.theorem_start_pos.line}-{eval_thm.theorem_start_pos.column}.json"
    )


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


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--coqstoq_loc", type=str, required=True)
    parser.add_argument("--split", type=str, required=True)
    parser.add_argument("--save_loc", type=str, required=True)
    parser.add_argument("--timeout", type=int, default=600)
    parser.add_argument("--slurm_conf", type=str)
    parser.add_argument("--n_workers", type=int)

    args = parser.parse_args()

    assert args.slurm_conf is not None or args.n_workers is not None

    coqstoq_loc = Path(args.coqstoq_loc)
    split = get_coqstoq_split(args.split)
    save_loc = Path(args.save_loc)

    set_rango_logger(__file__, logging.DEBUG)
    queue_loc, slurm_loc = get_queue_slurm_loc()
    fill_queue(queue_loc, split, coqstoq_loc, save_loc)

    module_command = "source unity-module-change-revert"
    opam_command = "module load opam/2.1.2"
    eval_opam_command = "eval $(opam env)"
    worker_command = f"python3 {WORKER_LOC} slurm --coqstoq_loc {coqstoq_loc} --save_loc {save_loc} --queue_loc {queue_loc} --timeout {args.timeout}"
    commands: list[str] = [
        module_command,
        opam_command,
        eval_opam_command,
        worker_command,
    ]

    if args.slurm_conf is not None:
        with open(args.slurm_conf, "r") as fin:
            slurm_yaml = yaml.safe_load(fin)
            slurm_conf = slurm_conf_from_yaml(slurm_yaml)

        slurm_conf.write_script(
            "eval-hammer",
            commands,
            slurm_loc,
        )
        subprocess.run(["sbatch", str(slurm_loc)])

    else:
        assert args.n_workers is not None
        print("Starting workers")
        run_local(worker_command, args.n_workers)
