from __future__ import annotations
from typing import Any
from dataclasses import dataclass

import os

from coqpyt.coq.base_file import CoqFile
from coqpyt.coq.lsp.structs import Goal, GoalAnswer
from data_management.splits import DataSplit, FileInfo

from parsy import string, regex, whitespace, seq, forward_declaration, Parser, peek

from data_management.splits import FileInfo
from util.util import get_fresh_path


term_p = forward_declaration()
expr_p_app = forward_declaration()
expr_p_var = forward_declaration()

__raw_name_p = regex(r"\w+") << whitespace.optional()
__reserved_p = (
    string("with")
    | string("end")
    | string("fix")
    | string("fun")
    | string("forall")
    | string("exists")
    | string("match")
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


def combine_param_set(vars: list[str], ty: str) -> list[Param]:
    return [Param(v, ty) for v in vars]


def join_lists(*args: list[Any]) -> list[Any]:
    result_list: list[Any] = []
    for a in args:
        result_list.extend(a)
    return result_list


__param_set_p_raw = seq(__name_p.at_least(1) << __colon_p, __name_p).combine(
    combine_param_set
)
__param_set_p_paren = parens(__param_set_p_raw)

__multi_param_set_p_paran = __param_set_p_paren.at_least(1).combine(join_lists)
params_p = __param_set_p_raw | __multi_param_set_p_paran


@dataclass
class Param:
    id: str
    ty: str


def combine_fix(id: str, params: list[Param], ty: str, body: Term) -> FixT:
    return FixT(id, params, ty, body)


__struct_arg_p = (
    string("{struct") << whitespace >> __name_p << string("}") << whitespace.optional()
)

__def_p = string(":=") << whitespace
__fix_p_raw = seq(
    string("fix") << whitespace >> __name_p,
    params_p << __struct_arg_p << __colon_p,
    __name_p,
    __def_p >> expr_p_app,
).combine(combine_fix)

fix_p = __fix_p_raw | parens(__fix_p_raw)


@dataclass
class FixT:
    id: str
    params: list[Param]
    ty: str
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


# class FunT:
#     def __init__(self, params: list[Param], body: Term) -> None:
#         self.params = params
#         self.body = body


abstraction_p = fix_p | var_p


Abstraction = FixT | VarT


def combine_app_p(abstr: Abstraction, args: list[Expr]) -> AppT:
    return AppT(abstr, args)


__app_p_raw = seq(abstraction_p, expr_p_var.at_least(1)).combine(combine_app_p)

app_p = __app_p_raw | parens(__app_p_raw)


@dataclass
class AppT:
    fn: Abstraction
    args: list[Expr]


def combine_match_branch(pattern: ConstrExpr, body: Expr) -> MatchBranch:
    return MatchBranch(pattern, body)


match_branch_p = seq(
    string("|") << whitespace >> constr_expr_p << string("=>") << whitespace,
    expr_p_app << whitespace.optional(),
).combine(combine_match_branch)


@dataclass
class MatchBranch:
    pattern: ConstrExpr
    body: Expr


def combine_match(expr: Expr, branches: list[MatchBranch]) -> MatchT:
    return MatchT(expr, branches)


__parens_expr_or_var_p = var_p | parens(expr_p_app)

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
    expr: Expr
    branches: list[MatchBranch]


Expr = FixT | MatchT | AppT | VarT
Term = FixT | MatchT | AppT | VarT | ProdT

term_p.become(app_p | fix_p | match_p | prod_p | var_p)
expr_p_app.become(app_p | fix_p | match_p | var_p)
expr_p_var.become(var_p | app_p | fix_p | match_p | var_p)


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


def has_hyp(goal: Goal) -> bool:
    return len(goal.hyps) > 0


def get_generalize_var(goal: Goal) -> str:
    if len(goal.hyps) == 0:
        raise HypsEmptyError("No vars to generalize.")
    for hyp in goal.hyps:
        for name in hyp.names:
            if __appears_in_hyp_or_goal(name, goal):
                return name
    return goal.hyps[0].names[0]


def get_fg_goal(goal: GoalAnswer) -> Goal:
    assert goal.goals is not None
    fg_goals = goal.goals.goals
    if len(fg_goals) == 0:
        raise EmptyFgGoalError("No foreground goals.")
    return fg_goals[0]


def get_norm_goal(data_loc: str, file_info: FileInfo, proof_prefix: str) -> Term:
    file_loc = os.path.join(data_loc, file_info.file)
    workspace_loc = os.path.join(data_loc, file_info.workspace)
    aux_file = get_fresh_path(".", "goal_aux.v")

    try:
        with open(aux_file, "w") as fout:
            fout.write(proof_prefix)
        with CoqFile(file_loc, workspace_loc) as coq_file:
            coq_file.run()
            goals = coq_file.current_goals
            fg_goal = get_fg_goal(goals)
            while has_hyp(fg_goal):
                generalize_var = get_generalize_var(fg_goal)
                last_step = len(coq_file.steps)
                step_text = f"\ngeneralize dependent {generalize_var}."
                coq_file.add_step(last_step - 1, step_text)
                coq_file.exec()
                goals = coq_file.current_goals
                fg_goal = get_fg_goal(goals)
            last_step = len(coq_file.steps)
            rid_notations = "\nUnset Printing Notations."
            coq_file.add_step(last_step - 1, rid_notations)
            simpl = "\ncbv."
            last_step = len(coq_file.steps)
            coq_file.add_step(last_step - 1, simpl)
            goals = coq_file.current_goals
            fg_goal = get_fg_goal(goals)
            return term_p.parse(fg_goal.ty)
    finally:
        if os.path.exists(aux_file):
            os.remove(aux_file)
