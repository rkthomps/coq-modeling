from __future__ import annotations
from typing import Any, Optional, Generator
from dataclasses import dataclass

import json
import time
import random
from tqdm import tqdm
import sys
import os
import shutil
import logging
import ipdb
import argparse
import multiprocessing as mp
from parsy import ParseError
import traceback

from coqpyt.coq.base_file import CoqFile
from coqpyt.coq.lsp.structs import Goal, Hyp, GoalAnswer
from coqpyt.coq.exceptions import InvalidChangeException
from data_management.splits import DataSplit, FileInfo

from data_management.splits import FileInfo, DataSplit, Split, split2str, str2split
from model_deployment.transform_ast import (
    StrTree,
    term_from_ast,
    get_body_from_definition,
)
from util.util import get_fresh_path, LOGGER
from util.coqpyt_utils import (
    get_proof_indices,
    replace_proof_with_admitted_stub,
    restore_proof_file,
    go_to_point,
    go_through_point,
    get_all_goals,
)



class EmptyFgGoalError(Exception):
    pass


class HypsEmptyError(Exception):
    pass


class GoalTermRecord:
    def __init__(
        self,
        term: StrTree,
        pretty_goal: str,
        proof: list[str],
        file_info: FileInfo,
        split: Split,
        proof_start_idx: int,
    ) -> None:
        """
        Proof start idx: inclusive
        Proof end idx: exclusive
        """
        self.term = term
        self.pretty_goal = pretty_goal
        self.proof = proof
        self.file_info = file_info
        self.split = split
        self.proof_start_idx = proof_start_idx

    def __hash__(self) -> int:
        return hash(
            (
                "GoalTermRecord",
                hash(self.term),
                self.pretty_goal,
                hash(tuple(self.proof)),
                hash(self.file_info),
                split2str(self.split),
                self.proof_start_idx,
            )
        )

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, GoalTermRecord):
            return False
        return hash(self) == hash(other)

    def to_json(self) -> Any:
        return {
            "term": self.term.to_json(),
            "pretty_goal": self.pretty_goal,
            "proof": self.proof,
            "file_info": self.file_info.to_json(),
            "split": split2str(self.split),
            "proof_start_idx": self.proof_start_idx,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> GoalTermRecord:
        term = StrTree.from_json(json_data["term"])
        pretty_goal = json_data["pretty_goal"]
        proof = json_data["proof"]
        file_info = FileInfo.from_json(json_data["file_info"])
        split = str2split(json_data["split"])
        proof_start_idx = json_data["proof_start_idx"]
        return cls(term, pretty_goal, proof, file_info, split, proof_start_idx)


class GoalTermDBPage:
    def __init__(self, records: list[GoalTermRecord]) -> None:
        self.records = records
        self.record_set = set([hash(r) for r in self.records])

    def add(self, record: GoalTermRecord) -> None:
        record_hash = hash(record)
        if record_hash in self.record_set:
            return
        self.records.append(record)
        self.record_set.add(record_hash)

    def size(self) -> int:
        return len(self.records)

    def merge(self, other: GoalTermDBPage) -> None:
        for record in other.records:
            self.add(record)

    def to_json(self) -> Any:
        return {"records": [r.to_json() for r in self.records]}

    def save(self, path: str) -> None:
        path_dirname = os.path.dirname(path)
        os.makedirs(path_dirname, exist_ok=True)
        with open(path, "w") as fout:
            fout.write(json.dumps(self.to_json()))

    @classmethod
    def empty(cls) -> GoalTermDBPage:
        return cls([])

    @classmethod
    def load(cls, path: str) -> GoalTermDBPage:
        with open(path, "r") as fin:
            json_data = json.load(fin)
            return cls.from_json(json_data)

    @classmethod
    def from_json(cls, json_data: Any) -> GoalTermDBPage:
        records = [GoalTermRecord.from_json(r) for r in json_data["records"]]
        return cls(records)


class GoalTermDB:
    SAVE_NAME = "goalDB"

    def __init__(
        self, pages: dict[int, GoalTermDBPage], completed_coqfiles: list[FileInfo]
    ) -> None:
        self.pages = pages  # This is the only thing keeping pages in memory if memory becomes a problem
        self.completed_coqfiles = set(completed_coqfiles)
        self.save_every = 1  # save after adding n coq files
        self.save_count = 0
        self.save_loc: Optional[str] = None

    def size(self) -> int:
        return sum([p.size() for _, p in self.pages.items()])

    def sample(self, n: int, seed: int = 1) -> list[GoalTermRecord]:
        random.seed(seed)
        sample_num = min(self.size(), n)
        records: list[GoalTermRecord] = []
        for _ in range(sample_num):
            page = random.choice(list(self.pages.values()))
            item = random.choice(page.records)
            records.append(item)
        return records

    def is_already_completed(self, file: FileInfo) -> bool:
        return file in self.completed_coqfiles

    def merge(self, other: GoalTermDB) -> None:
        for page_num, page in other.pages.items():
            if page_num in self.pages:
                self.pages[page_num].merge(page)
            else:
                self.pages[page_num] = page
        self.completed_coqfiles |= other.completed_coqfiles

    def add_record(self, record: GoalTermRecord) -> None:
        size = record.term.size()
        if size not in self.pages:
            self.pages[size] = GoalTermDBPage.empty()
        self.pages[size].add(record)

    def add_completed_coqfile(self, completed_file: FileInfo) -> None:
        self.completed_coqfiles.add(completed_file)

    def thump_completed_coqfile(
        self, completed_file: FileInfo, save_parent_dir: str
    ) -> None:
        self.completed_coqfiles.add(completed_file)
        self.save_count += 1
        if self.save_count == self.save_every:
            self.save_parent_dir(save_parent_dir)
            self.save_count = 0

    def to_json(self) -> Any:
        return {
            "pages": dict([(k, v.to_json()) for k, v in self.pages.items()]),
            "completed_coqfiles": [f.to_json() for f in self.completed_coqfiles],
        }

    def save(self, save_dir: str) -> Any:
        if os.path.exists(save_dir):
            raise FileExistsError(f"{save_dir} exists.")
        os.makedirs(save_dir)
        for page_len, page in self.pages.items():
            page_path = os.path.join(save_dir, str(page_len))
            page.save(page_path)
        completed_files_loc = os.path.join(save_dir, "completed_coqfiles")
        with open(completed_files_loc, "w") as fout:
            fout.write(json.dumps([f.to_json() for f in self.completed_coqfiles]))

    def save_parent_dir(self, save_parent_dir: str) -> Any:
        os.makedirs(save_parent_dir, exist_ok=True)
        if self.save_loc:
            shutil.rmtree(self.save_loc)
            self.save(self.save_loc)
        else:
            save_num = 0
            save_loc = os.path.join(save_parent_dir, f"{self.SAVE_NAME}_{save_num}")
            while os.path.exists(save_loc):
                save_num += 1
                save_loc = os.path.join(save_parent_dir, f"{self.SAVE_NAME}_{save_num}")
            self.save_loc = save_loc
            self.save(self.save_loc)

    @classmethod
    def empty(cls) -> GoalTermDB:
        return cls({}, [])

    @classmethod
    def load(cls, load_dir: str) -> GoalTermDB:
        completed_coqfiles_loc = os.path.join(load_dir, "completed_coqfiles")
        with open(completed_coqfiles_loc, "r") as fin:
            completed_coqfile_data = json.load(fin)
        completed_coqfiles = [FileInfo.from_json(f) for f in completed_coqfile_data]
        pages: dict[int, GoalTermDBPage] = {}
        for filename in os.listdir(load_dir):
            if filename == "completed_coqfiles":
                pass
            elif filename.isnumeric():
                page_num = int(filename)
                page_loc = os.path.join(load_dir, filename)
                pages[page_num] = GoalTermDBPage.load(page_loc)
            else:
                LOGGER.warning(
                    f"Unexpected file found in GoalTermDB directory: ", {filename}
                )
        return cls(pages, completed_coqfiles)

    @classmethod
    def load_dist(cls, load_dist_dir: str) -> GoalTermDB:
        merged_db = GoalTermDB.empty()
        for filename in os.listdir(load_dist_dir):
            file_loc = os.path.join(load_dist_dir, filename)
            db_fragment = GoalTermDB.load(file_loc)
            merged_db.merge(db_fragment)
        return merged_db

    @classmethod
    def create(
        cls, records: list[GoalTermRecord], completed_coqfiles: list[FileInfo]
    ) -> GoalTermDB:
        pages: dict[int, GoalTermDBPage] = {}
        for record in records:
            size = record.term.size()
            if size not in pages:
                pages[size] = GoalTermDBPage.empty()
            pages[size].add(record)
        return cls(pages, completed_coqfiles)


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
    for i in range(num_steps_added):
        added_step_idx = num_steps_added - i
        delete_idx = end_idx + added_step_idx
        coq_file.delete_step(delete_idx)


def get_norm_goal(
    tmp_file: str, proof_prefix: str, workspace_loc: str
) -> Optional[tuple[StrTree, str]]:
    """End is the step to evaluate through"""
    with open(tmp_file, "w") as fout:
        fout.write(proof_prefix)
    with CoqFile(
        os.path.abspath(tmp_file), workspace=os.path.abspath(workspace_loc)
    ) as coq_file:
        coq_file.run()
        if not coq_file.in_proof:
            return None
        end = len(coq_file.steps) - 1
        steps_added = 0
        go_through_point(coq_file, end)
        goals = coq_file.current_goals
        fg_goal = get_fg_goal(goals)
        pretty_goal = repr(fg_goal)
        cannot_generalize: set[str] = set()
        generalize_var = get_generalize_var(fg_goal, cannot_generalize)
        while generalize_var:
            cannot_generalize.add(generalize_var)
            step_text = f"\ngeneralize dependent {generalize_var}."
            try:
                coq_file.add_step(end + steps_added, step_text)
                coq_file.exec()
                steps_added += 1
                goals = coq_file.current_goals
                fg_goal = get_fg_goal(goals)
            except InvalidChangeException:
                pass
            generalize_var = get_generalize_var(fg_goal, cannot_generalize)
        rid_notations = "\nUnset Printing Notations."
        coq_file.add_step(end + steps_added, rid_notations)
        coq_file.exec()
        steps_added += 1
        simpl = "\ncbv."
        coq_file.add_step(end + steps_added, simpl)
        coq_file.exec()
        steps_added += 1
        goals = coq_file.current_goals
        fg_goal = get_fg_goal(goals)

    with open(tmp_file, "w") as fout:
        fout.write(proof_prefix + f"\nAdmitted.\n\nDefinition a := ({fg_goal.ty}).")

    with CoqFile(
        os.path.abspath(tmp_file), workspace=os.path.abspath(workspace_loc)
    ) as coq_file:
        ast = coq_file.steps[-1].ast.span
        ast_no_def = get_body_from_definition(ast)
        term_strtree = term_from_ast(ast_no_def).to_strtree()
        return term_strtree, pretty_goal


def __get_goal_len(coq_file: CoqFile) -> Optional[int]:
    cur_goals = coq_file.current_goals
    if cur_goals is None:
        return None
    if cur_goals.goals is None:
        return None
    all_goals = get_all_goals(cur_goals)
    return len(all_goals)


def __get_subproofs(coq_file: CoqFile, proof_index: int) -> list[Optional[list[str]]]:
    subproofs: list[Optional[list[str]]] = []
    goals_at_step: list[Optional[int]] = []
    go_through_point(coq_file, proof_index)
    assert coq_file.in_proof
    while coq_file.in_proof:
        cur_num_goals = __get_goal_len(coq_file)
        goals_at_step.append(cur_num_goals)
        coq_file.exec(1)

    steps = [s.text for s in coq_file.steps]
    subproofs: list[Optional[list[str]]] = []
    for i, start in enumerate(goals_at_step):
        if start is None:
            subproofs.append(None)
            continue
        cur_end = i + 1
        while cur_end < len(goals_at_step):
            test_goals = goals_at_step[cur_end]
            cur_end_goals = 0 if test_goals is None else test_goals
            if cur_end_goals < start:
                break
            cur_end += 1
        subproofs.append(steps[(proof_index + i + 1) : (proof_index + cur_end + 1)])
    return subproofs


def mine_coq_file_goals(
    coq_file: CoqFile,
    file_info: FileInfo,
    split: Split,
    data_loc: str,
) -> Generator[Optional[GoalTermRecord], None, None]:
    proof_indices = get_proof_indices(coq_file)
    temp_loc = get_fresh_path(".", "goal_aux.v")
    workspace_loc = os.path.join(data_loc, file_info.workspace)
    file_loc = os.path.join(data_loc, file_info.file)
    shutil.copy(file_loc, temp_loc)
    try:
        for proof_index in proof_indices:
            subproofs = __get_subproofs(coq_file, proof_index)
            num_proof_steps = 0
            while num_proof_steps < len(subproofs):
                subproof = subproofs[num_proof_steps]
                if subproof is None:
                    num_proof_steps += 1
                    continue
                proof_start_idx = proof_index + 1 + num_proof_steps
                prefix = "".join([s.text for s in coq_file.steps[:proof_start_idx]])
                try:
                    stree_w_goal = get_norm_goal(temp_loc, prefix, workspace_loc)
                except EmptyFgGoalError:
                    num_proof_steps += 1
                    continue
                except Exception as e:
                    LOGGER.warning(
                        f"Trouble processing {file_info.file} of n steps {len(coq_file.steps)} with exception {e.__class__}"
                    )
                    yield None
                    num_proof_steps += 1
                    continue
                if stree_w_goal is None:
                    break
                stree, goal = stree_w_goal
                if stree.has_unknown():
                    LOGGER.warning(f"AST Transform error in: {file_info.file}")
                record = GoalTermRecord(
                    stree, goal, subproof, file_info, split, proof_start_idx
                )
                yield record
                num_proof_steps += 1
    finally:
        os.remove(temp_loc)


# Don't want to load a new db every time.
def mine_file_goals(
    data_loc: str, file_info: FileInfo, db: GoalTermDB, split: Split, save_loc: str
) -> None:
    print("Processing", file_info.file)
    file_loc = os.path.abspath(os.path.join(data_loc, file_info.file))
    workspace_loc = os.path.abspath(os.path.join(data_loc, file_info.workspace))
    with CoqFile(file_loc, workspace=workspace_loc) as coq_file:
        if not coq_file.is_valid:
            LOGGER.warning(f"File {file_info.file} started invalid.")
            return
        try:
            files_records = mine_coq_file_goals(coq_file, file_info, split, data_loc)
            flawless = True
            prev_record = None
            for record in files_records:
                if record is None:
                    flawless = False
                    continue
                if prev_record and record.term == prev_record.term:
                    continue
                db.add_record(record)
                if record.term.has_unknown():
                    flawless = False
                prev_record = record
            if flawless:
                db.thump_completed_coqfile(file_info, save_loc)
        except Exception as e:
            traceback.print_exc()
            LOGGER.warning(
                f"Trouble processing {file_info.file} of n steps {len(coq_file.steps)} with exception {e.__class__}"
            )


__ARG = tuple[str, FileInfo, GoalTermDB, Split, str]


def get_mining_args(
    data_loc: str, data_split: DataSplit, goal_db: GoalTermDB, save_loc: str
) -> list[__ARG]:
    args: list[__ARG] = []
    for split in Split:
        file_list = data_split.get_file_list(Split.TRAIN)
        for file_info in file_list:
            args.append((data_loc, file_info, goal_db, split, save_loc))
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
    parser.add_argument(
        "--starting_db", "-s", type=str, help="Location of the initial goal term db."
    )
    parser.add_argument("data_split_loc", help="Path to saved data split.")
    parser.add_argument("data_loc", help="Path to coq dataset.")
    parser.add_argument("save_db", help="Path to save dbs")
    args = parser.parse_args(sys.argv[1:])

    num_procs = 1
    if args.num_procs:
        num_procs = args.num_procs

    if args.starting_db:
        initial_db = GoalTermDB.load_dist(args.starting_db)
    else:
        initial_db = GoalTermDB.empty()

    data_split = DataSplit.load(args.data_split_loc)
    mining_args = get_mining_args(args.data_loc, data_split, initial_db, args.save_db)
    with mp.Pool(num_procs) as pool:
        pool.starmap(mine_file_goals, mining_args)
    # for args in mining_args:
    #     mine_file_goals(*args)
