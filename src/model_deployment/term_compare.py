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

from coqpyt.coq.base_file import CoqFile, GoalAnswer
from coqpyt.coq.lsp.structs import Goal, Hyp
from coqpyt.coq.exceptions import InvalidStepException
from data_management.splits import DataSplit, FileInfo

from parsy import (
    string,
    regex,
    whitespace,
    seq,
    forward_declaration,
    Parser,
    peek,
    ParseError,
)

from data_management.splits import FileInfo, DataSplit, Split
from util.util import get_fresh_path, get_basic_logger

_logger = get_basic_logger(__name__)

term_p = forward_declaration()
term_p_var = forward_declaration()

__raw_name_p = regex(r"(\w|\.|')+") << whitespace.optional()
__reserved_p = (
    string("with")
    | string("end")
    | string("fix")
    | string("fun")
    | string("forall")
    | string("exists")
    | string("match")
    | string("fun")
).should_fail("reserved")
__name_p = peek(__reserved_p) >> __raw_name_p


def parens(p: Parser) -> Parser:
    return string("(") >> p << string(")") << whitespace.optional()


var_p = __name_p.map(lambda x: VarT(x))


@dataclass
class VarT:
    id: str


constr_expr_p = forward_declaration()


def combined_constr_app(cstr_name: str, cstr_exprs: list[ConstrExpr]) -> ConstructorApp:
    return ConstructorApp(cstr_name, cstr_exprs)


__constr_app_p_raw = seq(__name_p, constr_expr_p.at_least(1))
__constr_app_p = __constr_app_p_raw | parens(__constr_app_p_raw)


@dataclass
class ConstructorApp:
    constr: str
    arg: list[ConstrExpr]


constr_expr_p.become(__constr_app_p | var_p)

ConstrExpr = ConstructorApp | VarT


__colon_p = string(":") << whitespace


def combine_param_set(vars: list[str], ty: Term) -> list[Param]:
    return [Param(v, ty) for v in vars]


def join_lists(*args: list[Any]) -> list[Any]:
    result_list: list[Any] = []
    for a in args:
        result_list.extend(a)
    return result_list


__param_set_p_raw = seq(__name_p.at_least(1) << __colon_p, term_p).combine(
    combine_param_set
)
__param_set_p_paren = parens(__param_set_p_raw)

__multi_param_set_p_paren = __param_set_p_paren.at_least(1).combine(join_lists)
params_p = __param_set_p_raw | __multi_param_set_p_paren


@dataclass
class Param:
    id: str
    ty: Term


def combine_fix(id: str, params: list[Param], ty: str, body: Term) -> FixT:
    return FixT(id, params, ty, body)


__struct_arg_p = (
    string("{struct") << whitespace >> __name_p << string("}") << whitespace.optional()
)

__def_p = string(":=") << whitespace
__fix_p_raw = seq(
    string("fix") << whitespace >> __name_p,
    params_p << __struct_arg_p.optional() << __colon_p,
    term_p,
    __def_p >> term_p,
).combine(combine_fix)

fix_p = __fix_p_raw | parens(__fix_p_raw)


@dataclass
class FixT:
    id: str
    params: list[Param]
    ty: Term
    body: Term


def combine_prod(params: list[Param], body: Term) -> ProdT:
    return ProdT(params, body)


__prod_p_raw = seq(
    string("forall") << whitespace >> params_p, string(",") << whitespace >> term_p
).combine(combine_prod)

prod_p = __prod_p_raw | parens(__prod_p_raw)


@dataclass
class ProdT:
    params: list[Param]
    body: Term


# class ExistsT:
#     def __init__(self, params: list[Param], body: Term) -> None:
#         self.params = params
#         self.body = body


def combine_fun(params: list[Param], body: Term) -> FunT:
    return FunT(params, body)


__fun_p_raw = seq(
    string("fun") << whitespace >> params_p, string("=>") << whitespace >> term_p
).combine(combine_fun)

fun_p = __fun_p_raw | parens(__fun_p_raw)


@dataclass
class FunT:
    params: list[Param]
    body: Term


abstraction_p = fix_p | var_p | fun_p


Abstraction = FixT | VarT | FunT


def combine_app_p(abstr: Abstraction, args: list[Term]) -> AppT:
    return AppT(abstr, args)


__app_p_raw = seq(abstraction_p, term_p_var.at_least(1)).combine(combine_app_p)

app_p = __app_p_raw | parens(__app_p_raw)


@dataclass
class AppT:
    fn: Abstraction
    args: list[Term]


def combine_match_branch(pattern: ConstrExpr, body: Term) -> MatchBranch:
    return MatchBranch(pattern, body)


match_branch_p = seq(
    string("|") << whitespace >> constr_expr_p << string("=>") << whitespace,
    term_p << whitespace.optional(),
).combine(combine_match_branch)


@dataclass
class MatchBranch:
    pattern: ConstrExpr
    body: Term


def combine_match(expr: Term, branches: list[MatchBranch]) -> MatchT:
    return MatchT(expr, branches)


__parens_expr_or_var_p = var_p | parens(term_p)

__match_p_raw = seq(
    string("match")
    << whitespace
    >> __parens_expr_or_var_p
    << string("with")
    << whitespace,
    match_branch_p.at_least(1) << string("end") << whitespace.optional(),
).combine(combine_match)

match_p = __match_p_raw | parens(__match_p_raw)


@dataclass
class MatchT:
    expr: Term
    branches: list[MatchBranch]


Term = FixT | MatchT | AppT | VarT | ProdT | FunT

__term_p_raw = app_p | fix_p | fun_p | match_p | prod_p | var_p
term_p.become(__term_p_raw | parens(__term_p_raw))

__term_p_var = var_p | app_p | fix_p | fun_p | match_p | prod_p
term_p_var.become(__term_p_var | parens(__term_p_var))


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
            except InvalidStepException:
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
            print("got it!")
            return parsed_term
        except ParseError:
            print(len(fg_goal.ty))
            if len(fg_goal.ty) < 400:
                print(fg_goal.ty)
    finally:
        __restore_coq_file(coq_file, end, steps_added)


def __clear_coq_file(coq_file: CoqFile) -> list[str]:
    step_bank: list[str] = []
    while len(coq_file.steps) > 0:
        step_bank.insert(0, coq_file.steps[-1].text)
        coq_file.delete_step(len(coq_file.steps) - 1)
    return step_bank


def mine_norm_goals(data_loc: str, data_split: DataSplit) -> None:
    file_list = data_split.get_file_list(data_loc, Split.TRAIN)
    random.seed(2)
    random.shuffle(file_list)
    temp_loc = get_fresh_path(".", "goal_aux.v")
    for file_info in file_list:
        print("Processing", file_info.file)
        file_loc = os.path.join(data_loc, file_info.file)
        workspace_loc = os.path.join(data_loc, file_info.workspace)
        with CoqFile(file_loc, workspace=workspace_loc) as coq_file:
            steps = [s.text for s in coq_file.steps]
        shutil.copy(file_loc, temp_loc)
        with CoqFile(temp_loc, workspace=workspace_loc) as coq_file:
            if not coq_file.is_valid:
                _logger.warning(f"{file_info.file} not valid initially. Skipping.")
                continue

            removed_steps = __clear_coq_file(coq_file)
            for i, step in enumerate(removed_steps):
                coq_file.add_step(i - 1, step)
                __exec_to(coq_file, i + 1)
                if coq_file.in_proof:
                    if (
                        coq_file.current_goals is None
                        or coq_file.current_goals.goals is None
                        or len(coq_file.current_goals.goals.goals) == 0
                    ):
                        continue
                    get_norm_goal(coq_file, i + 1)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Parser to make a database of proof states."
    )
    parser.add_argument("data_split_loc", help="Path to saved data split.")
    parser.add_argument("data_loc", help="Path to coq dataset.")
    args = parser.parse_args(sys.argv[1:])

    data_split = DataSplit.load(args.data_split_loc)
    mine_norm_goals(args.data_loc, data_split)
