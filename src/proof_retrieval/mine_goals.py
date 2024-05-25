from __future__ import annotations
from typing import Generator, Optional, Any
import multiprocessing as mp
from threading import Thread
from dataclasses import dataclass
import random
import sys
import os
import ipdb
import time
import traceback
import argparse
import json

from coqpyt.coq.base_file import CoqFile
from coqpyt.coq.structs import Step, GoalAnswer
from coqpyt.coq.lsp.structs import Goal, RangedSpan, Hyp
from coqpyt.lsp.structs import (
    TextDocumentIdentifier,
    VersionedTextDocumentIdentifier,
    TextDocumentContentChangeEvent,
    TextDocumentItem,
    Position,
    Range,
)

from model_deployment.fast_client import FastLspClient

# from coqpyt.coq.lsp.client import CoqLspClient
from data_management.splits import FileInfo, Split, DataSplit
from proof_retrieval.transform_ast import (
    term_from_ast,
    get_body_from_definition,
    StrTree,
)
from util.coqpyt_utils import get_all_goals
from util.util import get_fresh_path, get_basic_logger

_logger = get_basic_logger(__name__)


def get_contents(file: str) -> str:
    with open(file, "r") as fin:
        return fin.read()


def get_generalize_targets(goal_answer: GoalAnswer) -> list[str]:
    all_goals = get_all_goals(goal_answer)
    all_hyps: set[str] = set()
    for goal in all_goals:
        for h in goal.hyps:
            all_hyps |= set(h.names)
    return list(all_hyps)


class EmptyFgGoalError(Exception):
    pass


@dataclass
class GoalRecord:
    step_idx: int
    proof: list[str]
    pretty_goal: str
    term: StrTree

    def to_json(self) -> Any:
        return {
            "step_idx": self.step_idx,
            "proof": self.proof,
            "pretty_goal": self.pretty_goal,
            "term": self.term.to_json(),
        }

    @classmethod
    def from_json(cls, json_data: Any) -> GoalRecord:
        term = StrTree.from_json(json_data["term"])
        return cls(
            json_data["step_idx"], json_data["proof"], json_data["pretty_goal"], term
        )


@dataclass
class FileGoals:
    info: FileInfo
    records: list[GoalRecord]

    def save(self, path: str) -> None:
        parent = os.path.dirname(path)
        os.makedirs(parent, exist_ok=True)
        with open(path, "w") as fout:
            fout.write(json.dumps(self.to_json()))

    def to_json(self) -> Any:
        return {
            "info": self.info.to_json(),
            "records": [r.to_json() for r in self.records],
        }

    @classmethod
    def from_json(cls, json_data: Any) -> FileGoals:
        info = FileInfo.from_json(json_data["info"])
        records = [GoalRecord.from_json(r) for r in json_data["records"]]
        return cls(info, records)

    @classmethod
    def load(cls, path: str) -> FileGoals:
        with open(path, "r") as fin:
            json_data = json.load(fin)
            return cls.from_json(json_data)


def get_fg_goal(goal: GoalAnswer) -> Goal:
    assert goal.goals is not None
    fg_goals = goal.goals.goals
    if len(fg_goals) == 0:
        raise EmptyFgGoalError("No foreground goals.")
    return fg_goals[0]


def fmt_hyp(h: Hyp) -> str:
    lhs = " ".join(h.names)
    rhs = h.ty
    return f"({lhs} : {rhs})"


def fix_reserved_ids(g: Goal) -> Goal:
    """
    Hack for when ids are reserved in the goal
    i.e. _k_ in repos/david-jao-zfc-coq/binomial.v
    """
    hs = g.hyps
    cur_body = g.ty
    new_hyps: list[Hyp] = []
    tys: list[str] = [h.ty for h in hs]
    for i, h in enumerate(hs):
        h_new_names: list[str] = []
        for name in h.names:
            if name.startswith("_"):
                new_name = name.lstrip("_")
                cur_body = cur_body.replace(name, new_name)
                for j in range(i, len(hs)):
                    tys[j] = tys[j].replace(name, new_name)
                h_new_names.append(new_name)
            else:
                h_new_names.append(name)
        new_hyps.append(Hyp(h_new_names, tys[i]))
    return Goal(new_hyps, cur_body)


def get_goal_record(
    client: FastLspClient,
    doc_uri: str,
    doc_version: int,
    end_pos: Position,
    steps: list[Step],
    step_idx: int,
    goal_bank: dict[int, Optional[GoalAnswer]],
) -> tuple[Optional[GoalRecord], int]:
    prefix = "".join([s.text for s in steps[: (step_idx + 1)]])
    remaining_file_steps = steps[(step_idx + 1) :]
    if step_idx in goal_bank:
        goals = goal_bank[step_idx]
    else:
        doc_version += 1
        client.didChange(
            VersionedTextDocumentIdentifier(doc_uri, doc_version),
            [TextDocumentContentChangeEvent(None, None, prefix)],
        )
        goal_pos = Position(end_pos.line + 1, 0)
        goals = client.proof_goals(TextDocumentIdentifier(doc_uri), goal_pos)
        goal_bank[step_idx] = goals

    if goals is None:
        return None, doc_version

    if goals.goals is None:
        return None, doc_version

    all_goals = get_all_goals(goals)
    if len(all_goals) == 0:
        return None, doc_version

    subproof: list[str] = []
    for i, step in enumerate(remaining_file_steps):
        subproof.append(step.text)
        added_index = step_idx + 1 + i
        if added_index in goal_bank:
            new_goals = goal_bank[added_index]
        else:
            new_subproof = "".join(subproof)
            new_lines = new_subproof.count("\n")
            new_prefix = prefix + new_subproof
            doc_version += 1
            client.didChange(
                VersionedTextDocumentIdentifier(doc_uri, doc_version),
                [TextDocumentContentChangeEvent(None, None, new_prefix)],
            )
            goal_pos = Position(step.ast.range.end.line + new_lines, 0)
            new_goals = client.proof_goals(TextDocumentIdentifier(doc_uri), goal_pos)
            goal_bank[added_index] = new_goals

        if new_goals is None or new_goals.goals is None:
            break
        if len(get_all_goals(new_goals)) < len(all_goals):
            break

    fg_goals = goals.goals.goals
    if len(fg_goals) == 0:
        return GoalRecord(step_idx, subproof, "", StrTree("empty-fg", [])), doc_version

    pretty_goal = repr(fg_goals[0])

    # Get Norm Tree
    all_hyps = get_generalize_targets(goals)
    steps_to_add: list[str] = (
        ["Set Printing All.", "Unset Printing Notations."]
        + [f"generalize dependent {h}." for h in all_hyps]
        + ["cbn."]
    )
    add_str = "\n".join(steps_to_add)
    doc_version += 1
    client.didChange(
        VersionedTextDocumentIdentifier(doc_uri, doc_version),
        [TextDocumentContentChangeEvent(None, None, prefix + "\n" + add_str)],
    )
    norm_goal_pos = Position(end_pos.line + len(steps_to_add) + 1, 0)
    goals = client.proof_goals(TextDocumentIdentifier(doc_uri), norm_goal_pos)

    fg_goal = get_fg_goal(goals)
    adjusted_fg_goal = fix_reserved_ids(fg_goal)
    hyp_str = " ".join([fmt_hyp(h) for h in adjusted_fg_goal.hyps])
    text = f"Definition a {hyp_str} := ({adjusted_fg_goal.ty})."

    doc_version += 1
    client.didChange(
        VersionedTextDocumentIdentifier(doc_uri, doc_version),
        [TextDocumentContentChangeEvent(None, None, text)],
    )

    new_ast = client.get_document(TextDocumentIdentifier(doc_uri))
    try:
        term = term_from_ast(get_body_from_definition(new_ast.spans[-2].span))
    except TypeError:
        _logger.error("Typeerror in file")
        raise TypeError("typerror")

    return GoalRecord(step_idx, subproof, pretty_goal, term.to_strtree()), doc_version


def get_file_goals(
    data_loc: str, file_info: FileInfo, thread_result: GoalThreadReturn, timeout: int
) -> None:
    file_abs = os.path.abspath(os.path.join(data_loc, file_info.file))
    workspace_abs = os.path.abspath(os.path.join(data_loc, file_info.workspace))
    with CoqFile(
        file_abs, workspace=workspace_abs, low_verbosity=False, timeout=timeout
    ) as coq_file:
        steps = coq_file.steps
    tmp_file = get_fresh_path(".", "goal_aux.v")
    client_uri = f"file://{workspace_abs}"
    doc_uri = f"file://{tmp_file}"
    client = FastLspClient(client_uri, timeout=timeout)

    try:
        goal_bank: dict[int, Optional[GoalAnswer]] = {}
        version = 0
        version += 1
        records: list[GoalRecord] = []
        client.didOpen(
            TextDocumentItem(doc_uri, "coq", version, get_contents(file_abs))
        )
        for i in range(1, len(steps)):
            record, version = get_goal_record(
                client,
                doc_uri,
                version,
                steps[i].ast.range.end,
                steps,
                i,
                goal_bank,
            )
            if record:
                records.append(record)
        thread_result.file_goals = FileGoals(file_info, records)
        return
    finally:
        traceback.print_exc()
        client.shutdown()
        client.exit()


@dataclass
class GoalThreadReturn:
    file_goals: Optional[FileGoals]


def compute_file_goals(
    data_loc: str, file_info: FileInfo, save_loc: str, timeout: int
) -> None:
    save_name = os.path.join(save_loc, file_info.dp_name)
    if os.path.exists(save_name):
        _logger.info(f"{save_name} exists. Continuing")
        return
    _logger.info(f"Processing {file_info.dp_name}")

    file_loc = os.path.abspath(os.path.join(data_loc, file_info.file))
    workspace_loc = os.path.abspath(os.path.join(data_loc, file_info.workspace))
    with CoqFile(file_loc, workspace=workspace_loc, timeout=timeout) as coq_file:
        if not coq_file.is_valid:
            _logger.warning(f"{file_info.file} not valid.")
            return
        num_steps = len(coq_file.steps)

    ret_obj = GoalThreadReturn(None)
    goal_thread = Thread(
        target=get_file_goals, args=(data_loc, file_info, ret_obj, timeout)
    )
    goal_thread.start()
    goal_thread.join(timeout * num_steps)
    if ret_obj.file_goals:
        if len(ret_obj.file_goals.records) == 0:
            _logger.debug(f"Empty set of records for file: {file_info.file}")
        else:
            ret_obj.file_goals.save(save_name)
    else:
        _logger.debug(f"Timeout or error when processing {file_info.file}")


__ARG = tuple[str, FileInfo, str, int]

new_repos = {
    "repos/coq-community-corn",
    "repos/coq-community-gaia",
}


def get_args(
    data_loc: str, data_split: DataSplit, save_loc: str, timeout: int
) -> list[__ARG]:
    args: list[__ARG] = []
    for split in Split:
        for file_info in data_split.get_file_list(split):
            if (
                file_info.repository in new_repos
                or split == Split.VAL
                or split == Split.TEST
            ):
                args.append((data_loc, file_info, save_loc, timeout))
    args.reverse()
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
    parser.add_argument("save_goals", help="Path to save goals")
    parser.add_argument(
        "timeout", type=int, help="Timeout (seconfds) for getting a single file's goals"
    )
    args = parser.parse_args(sys.argv[1:])

    num_procs = 1
    if args.num_procs:
        num_procs = args.num_procs

    sys.setrecursionlimit(1500)
    data_split = DataSplit.load(args.data_split_loc)
    mining_args = get_args(args.data_loc, data_split, args.save_goals, args.timeout)

    # for arg_tuple in mining_args:
    #     compute_file_goals(*arg_tuple)

    with mp.Pool(num_procs) as pool:
        pool.starmap(compute_file_goals, mining_args)
