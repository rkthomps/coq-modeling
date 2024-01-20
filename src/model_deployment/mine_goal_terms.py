from __future__ import annotations
from typing import Any, Optional
from dataclasses import dataclass

import time
import random
from tqdm import tqdm
import sys
import os
import shutil
import ipdb
import argparse
import multiprocessing as mp

from coqpyt.coq.base_file import CoqFile
from coqpyt.coq.lsp.structs import Goal, Hyp, GoalAnswer
from coqpyt.coq.exceptions import InvalidChangeException
from data_management.splits import DataSplit, FileInfo

from data_management.splits import FileInfo, DataSplit, Split
from util.util import get_fresh_path, get_basic_logger
from util.coqpyt_utils import (
    get_proof_indices,
    replace_proof_with_admitted_stub,
    restore_proof_file,
)

_logger = get_basic_logger(__name__)


class EmptyFgGoalError(Exception):
    pass


class HypsEmptyError(Exception):
    pass


def __appears_in_hyp_or_goal(var: str, goal: Goal) -> bool:
    for hyp in goal.hyps:
        if var in hyp.ty:
            return True
    if var in goal.ty:
        return True
    return False


def get_generalize_var(goal: Goal, cannot_generalize: set[str]) -> Optional[str]:
    default_candidate: Optional[str] = None
    for hyp in goal.hyps:
        for name in hyp.names:
            if name in cannot_generalize:
                continue
            if __appears_in_hyp_or_goal(name, goal):
                return name
            default_candidate = name
    return default_candidate


def get_fg_goal(goal: GoalAnswer) -> Goal:
    assert goal.goals is not None
    fg_goals = goal.goals.goals
    if len(fg_goals) == 0:
        raise EmptyFgGoalError("No foreground goals.")
    return fg_goals[0]


def __restore_coq_file(coq_file: CoqFile, end_idx: int, num_steps_added: int) -> None:
    for i in range(1, num_steps_added + 1):
        added_step_idx = num_steps_added - i
        delete_idx = end_idx + added_step_idx
        coq_file.delete_step(delete_idx)


def __exec_to(coq_file: CoqFile, idx: int) -> None:
    while coq_file.steps_taken < idx:
        coq_file.exec()


def get_norm_goal(coq_file: CoqFile, end: int) -> Term:
    steps_added = 0
    try:
        __exec_to(coq_file, end)
        goals = coq_file.current_goals
        fg_goal = get_fg_goal(goals)
        cannot_generalize: set[str] = set()
        generalize_var = get_generalize_var(fg_goal, cannot_generalize)
        while generalize_var:
            step_text = f"\ngeneralize dependent {generalize_var}."
            try:
                coq_file.add_step(end + steps_added - 1, step_text)
                coq_file.exec()
                steps_added += 1
                goals = coq_file.current_goals
                fg_goal = get_fg_goal(goals)
            except InvalidChangeException:
                cannot_generalize.add(generalize_var)
            generalize_var = get_generalize_var(fg_goal, cannot_generalize)
        rid_notations = "\nUnset Printing Notations."
        coq_file.add_step(end + steps_added - 1, rid_notations)
        coq_file.exec()
        steps_added += 1
        simpl = "\ncbv."
        coq_file.add_step(end + steps_added - 1, simpl)
        coq_file.exec()
        steps_added += 1
        goals = coq_file.current_goals
        fg_goal = get_fg_goal(goals)
        try:
            parsed_term = term_p.parse(fg_goal.ty)
            return parsed_term
        except ParseError:
            print(len(fg_goal.ty))
            if len(fg_goal.ty) < 400:
                print(fg_goal.ty)
    finally:
        __restore_coq_file(coq_file, end, steps_added)


def __mine_file_goals(coq_file: CoqFile) -> None:
    proof_indices = get_proof_indices(coq_file)
    for proof_index in proof_indices:
        orig_steps = replace_proof_with_admitted_stub(coq_file, proof_index)
        try:
            for i, step in enumerate(orig_steps[:-1]):
                coq_file.add_step(proof_index + i, step)
                try:
                    get_norm_goal(coq_file, proof_index + i + 1)
                except EmptyFgGoalError:
                    continue
        finally:
            restore_proof_file(coq_file, proof_index, orig_steps)


def mine_file_goals(data_loc: str, file_info: FileInfo) -> None:
    print("Processing", file_info.file)
    file_loc = os.path.join(data_loc, file_info.file)
    workspace_loc = os.path.join(data_loc, file_info.workspace)
    temp_loc = get_fresh_path(".", "goal_aux.v")
    shutil.copy(file_loc, temp_loc)
    try:
        with CoqFile(temp_loc, workspace=workspace_loc) as coq_file:
            __mine_file_goals(coq_file)
    finally:
        if os.path.exists(temp_loc):
            os.remove(temp_loc)


__ARG = tuple[str, FileInfo]


def get_mining_args(data_loc: str, data_split: DataSplit) -> list[__ARG]:
    args: list[__ARG] = []
    file_list = data_split.get_file_list(data_loc, Split.TRAIN)
    random.seed(2)
    random.shuffle(file_list)
    for file_info in file_list:
        args.append((data_loc, file_info))
    return args


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Parser to make a database of proof states."
    )
    parser.add_argument(
        "--num_procs",
        "-n",
        type=int,
        help="Number of processes to use to mine the normalized goals.",
    )
    parser.add_argument("data_split_loc", help="Path to saved data split.")
    parser.add_argument("data_loc", help="Path to coq dataset.")
    args = parser.parse_args(sys.argv[1:])

    num_procs = 1
    if args.num_procs:
        num_procs = args.num_procs

    data_split = DataSplit.load(args.data_split_loc)
    mining_args = get_mining_args(args.data_loc, data_split)
    with mp.Pool(num_procs) as pool:
        pool.starmap(mine_file_goals, mining_args)
