from __future__ import annotations
from typing import Any
from dataclasses import dataclass

from coqpyt.coq.base_file import CoqFile, GoalAnswer
from data_management.splits import DataSplit, FileInfo

from parsy import string, regex, whitespace, seq, forward_declaration, Parser, peek

# drive

from data_management.splits import FileInfo


term_p = forward_declaration()
expr_p = forward_declaration()

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
    __def_p >> expr_p,
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


__app_p_raw = seq(abstraction_p, expr_p.at_least(1)).combine(combine_app_p)

app_p = __app_p_raw | parens(__app_p_raw)


@dataclass
class AppT:
    fn: Abstraction
    args: list[Expr]


def combine_match_branch(pattern: ConstrExpr, body: Expr) -> MatchBranch:
    return MatchBranch(pattern, body)


match_branch_p = seq(
    string("|") << whitespace >> constr_expr_p << string("=>") << whitespace,
    expr_p << whitespace.optional(),
).combine(combine_match_branch)


@dataclass
class MatchBranch:
    pattern: ConstrExpr
    body: Expr


def combine_match(expr: Expr, branches: list[MatchBranch]) -> MatchT:
    return MatchT(expr, branches)


__parens_expr_or_var_p = var_p | parens(expr_p)

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
expr_p.become(app_p | fix_p | match_p | var_p)


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
