from typing import Any

from model_deployment.goal_term import (
    VarT,
    ParamT,
    ConstructorApp,
    FixT,
    ProdT,
    FunT,
    AppT,
    MatchBranchT,
    MatchT,
    Abstraction,
    ConstrExpr,
    Term,
)

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

constr_expr_p = forward_declaration()


def combined_constr_app(cstr_name: str, cstr_exprs: list[ConstrExpr]) -> ConstructorApp:
    return ConstructorApp(cstr_name, cstr_exprs)


__constr_app_p_raw = seq(__name_p, constr_expr_p.at_least(1))
__constr_app_p = __constr_app_p_raw | parens(__constr_app_p_raw)

constr_expr_p.become(__constr_app_p | var_p)

__colon_p = string(":") << whitespace


def combine_param_set(vars: list[str], ty: Term) -> list[ParamT]:
    return [ParamT(v, ty) for v in vars]


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


def combine_fix(id: str, params: list[ParamT], ty: Term, body: Term) -> FixT:
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


def combine_prod(params: list[ParamT], body: Term) -> ProdT:
    return ProdT(params, body)


__prod_p_raw = seq(
    string("forall") << whitespace >> params_p, string(",") << whitespace >> term_p
).combine(combine_prod)

prod_p = __prod_p_raw | parens(__prod_p_raw)


def combine_fun(params: list[ParamT], body: Term) -> FunT:
    return FunT(params, body)


__fun_p_raw = seq(
    string("fun") << whitespace >> params_p, string("=>") << whitespace >> term_p
).combine(combine_fun)

fun_p = __fun_p_raw | parens(__fun_p_raw)


abstraction_p = fix_p | var_p | fun_p


def combine_app_p(abstr: Abstraction, args: list[Term]) -> AppT:
    return AppT(abstr, args)


__app_p_raw = seq(abstraction_p, term_p_var.at_least(1)).combine(combine_app_p)

app_p = __app_p_raw | parens(__app_p_raw)


def combine_match_branch(pattern: ConstrExpr, body: Term) -> MatchBranchT:
    return MatchBranchT(pattern, body)


match_branch_p = seq(
    string("|") << whitespace >> constr_expr_p << string("=>") << whitespace,
    term_p << whitespace.optional(),
).combine(combine_match_branch)


def combine_match(expr: Term, branches: list[MatchBranchT]) -> MatchT:
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

__term_p_raw = app_p | fix_p | fun_p | match_p | prod_p | var_p
term_p.become(__term_p_raw | parens(__term_p_raw))

__term_p_var = var_p | app_p | fix_p | fun_p | match_p | prod_p
term_p_var.become(__term_p_var | parens(__term_p_var))
