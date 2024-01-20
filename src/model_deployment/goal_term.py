from __future__ import annotations
from typing import Any, Optional
import json
from dataclasses import dataclass


class VarT:
    ALIAS = "VAR"

    def __init__(self, id: str) -> None:
        self.id = id

    def get_key(self) -> str:
        return f"key: {self.id}"

    def get_subterms(self) -> list[Term]:
        return []

    def to_string(self) -> str:
        return self.id

    def to_json(self) -> Any:
        return {"id": self.id}

    @classmethod
    def from_json(cls, json_data: Any) -> VarT:
        return cls(json_data["id"])


class ConstructorApp:
    ALIAS = "Constructor App"

    def __init__(self, constr: str, args: list[ConstrExpr]) -> None:
        self.constr = constr
        self.args = args

    def get_key(self) -> str:
        return f"const: {self.to_string()}"

    def to_string(self) -> str:
        return f"({self.constr}" + " ".join([a.to_string() for a in self.args]) + ")"

    def to_json(self) -> Any:
        return {
            "constr": self.constr,
            "args": [constr_expr_to_json(ce) for ce in self.args],
        }

    @classmethod
    def from_json(cls, json_data: Any) -> ConstructorApp:
        args = [constr_expr_from_json(ce) for ce in json_data["args"]]
        return cls(json_data["constr"], args)


ConstrExpr = ConstructorApp | VarT


def constr_expr_from_json(json_data: Any) -> ConstrExpr:
    attempted_alias = json_data["alias"]
    match attempted_alias:
        case ConstructorApp.ALIAS:
            return ConstructorApp.from_json(json_data)
        case VarT.ALIAS:
            return VarT.from_json(json_data)
        case _:
            raise ValueError(f"Unexpected alias for constr expr: {attempted_alias}")


def constr_expr_to_json(constr_expr: ConstrExpr) -> Any:
    return {"alias": constr_expr.ALIAS} | constr_expr.to_json()


class ParamT:
    ALIAS = "PARAM"

    def __init__(self, id: str, ty: Term) -> None:
        self.id = id
        self.ty = ty

    def get_key(self) -> str:
        return f"param: {self.id}"

    def get_subterms(self) -> list[Term]:
        return [self.ty]

    def to_json(self) -> Any:
        return {
            "id": self.id,
            "ty": term_to_json(self.ty),
        }

    @classmethod
    def from_json(cls, json_data: Any) -> ParamT:
        return cls(json_data["id"], term_from_json(json_data["ty"]))


@dataclass
class FixT:
    ALIAS = "FIX"

    def __init__(self, id: str, params: list[ParamT], ty: Term, body: Term) -> None:
        self.id = id
        self.params = params
        self.ty = ty
        self.body = body

    def get_key(self) -> str:
        return f"fix: {self.id}"

    def get_subterms(self) -> list[Term]:
        return self.params + [self.ty, self.body]

    def to_json(self) -> Any:
        return {
            "id": self.id,
            "params": [p.to_json() for p in self.params],
            "ty": term_to_json(self.ty),
            "body": term_to_json(self.body),
        }

    @classmethod
    def from_json(cls, json_data: Any) -> FixT:
        params = [ParamT.from_json(p) for p in json_data["params"]]
        ty = term_from_json(json_data["ty"])
        body = term_from_json(json_data["body"])
        return cls(json_data["id"], params, ty, body)


@dataclass
class ProdT:
    ALIAS = "PROD"

    def __init__(self, params: list[ParamT], body: Term) -> None:
        self.params = params
        self.body = body

    def get_key(self) -> str:
        return f"prod: "

    def get_subterms(self) -> list[Term]:
        return self.params + [self.body]

    def to_json(self) -> Any:
        return {
            "params": [p.to_json() for p in self.params],
            "body": term_to_json(self.body),
        }

    @classmethod
    def from_json(cls, json_data: Any) -> ProdT:
        params = [ParamT.from_json(p) for p in json_data["params"]]
        body = term_from_json(json_data["body"])
        return cls(params, body)


# class ExistsT:
#     def __init__(self, params: list[Param], body: Term) -> None:
#         self.params = params
#         self.body = body


@dataclass
class FunT:
    ALIAS = "FUN"

    def __init__(self, params: list[ParamT], body: Term) -> None:
        self.params = params
        self.body = body

    def get_key(self) -> str:
        return f"fun: "

    def get_subterms(self) -> list[Term]:
        return self.params + [self.body]

    def to_json(self) -> Any:
        return {
            "params": [p.to_json() for p in self.params],
            "body": term_to_json(self.body),
        }

    @classmethod
    def from_json(cls, json_data: Any) -> FunT:
        params = [ParamT.from_json(p) for p in json_data["params"]]
        body = term_from_json(json_data["body"])
        return cls(params, body)


Abstraction = FixT | VarT | FunT


def abstraction_to_json(abstraction: Abstraction) -> Any:
    return {"alias": abstraction.ALIAS} | abstraction.to_json()


def abstraction_from_json(json_data: Any) -> Abstraction:
    attempted_alias = json_data["alias"]
    match attempted_alias:
        case FixT.ALIAS:
            return FixT.from_json(json_data)
        case VarT.ALIAS:
            return VarT.from_json(json_data)
        case FunT.ALIAS:
            return FunT.from_json(json_data)
        case _:
            raise ValueError(f"Unknown abstraction alias {attempted_alias}")


@dataclass
class AppT:
    ALIAS = "APP"

    def __init__(self, fn: Abstraction, args: list[Term]) -> None:
        self.fn = fn
        self.args = args

    def get_key(self) -> str:
        return f"app: {self.fn.get_key()}"

    def get_subterms(self) -> list[Term]:
        return self.fn.get_subterms() + self.args

    def to_json(self) -> Any:
        return {
            "fn": abstraction_to_json(self.fn),
            "args": [term_to_json(t) for t in self.args],
        }

    @classmethod
    def from_json(cls, json_data: Any) -> AppT:
        fn = abstraction_from_json(json_data["fn"])
        args = [term_from_json(t) for t in json_data["args"]]
        return cls(fn, args)


@dataclass
class MatchBranchT:
    ALIAS = "MATCH BRANCH"

    def __init__(self, pattern: ConstrExpr, body: Term) -> None:
        self.pattern = pattern
        self.body = body

    def get_key(self) -> str:
        return self.pattern.get_key()

    def get_subterms(self) -> list[Term]:
        return [self.body]

    def to_json(self) -> Any:
        return {
            "pattern": constr_expr_to_json(self.pattern),
            "body": term_to_json(self.body),
        }

    @classmethod
    def from_json(cls, json_data: Any) -> MatchBranchT:
        pattern = constr_expr_from_json(json_data["pattern"])
        body = term_from_json(json_data["body"])
        return cls(pattern, body)


@dataclass
class MatchT:
    ALIAS = "MATCH"

    def __init__(self, expr: Term, branches: list[MatchBranchT]) -> None:
        self.expr = expr
        self.branches = branches

    def get_key(self) -> str:
        return f"match"

    def get_subterms(self) -> list[Term]:
        return [self.expr] + self.branches

    def to_json(self) -> Any:
        return {
            "expr": term_to_json(self.expr),
            "branches": [mb.to_json() for mb in self.branches],
        }

    @classmethod
    def from_json(cls, json_data: Any) -> MatchT:
        expr = term_from_json(json_data["expr"])
        branches = [MatchBranchT.from_json(mb) for mb in json_data["branches"]]
        return cls(expr, branches)


Term = FixT | MatchT | AppT | VarT | ProdT | FunT | ParamT | MatchBranchT


def term_to_json(term: Term) -> Any:
    return {"alias": term.ALIAS} | term.to_json()


def term_to_str(term: Term) -> str:
    return json.dumps(term_to_json(term))


def term_from_json(json_data: Any) -> Term:
    attempted_alias = json_data["alias"]
    match attempted_alias:
        case FixT.ALIAS:
            return FixT.from_json(json_data)
        case MatchT.ALIAS:
            return MatchT.from_json(json_data)
        case AppT.ALIAS:
            return AppT.from_json(json_data)
        case VarT.ALIAS:
            return VarT.from_json(json_data)
        case ProdT.ALIAS:
            return ProdT.from_json(json_data)
        case FunT.ALIAS:
            return FunT.from_json(json_data)
        case ParamT.ALIAS:
            return ParamT.from_json(json_data)
        case MatchBranchT.ALIAS:
            return MatchBranchT.from_json(json_data)
        case _:
            raise ValueError(f"Cannot find term type for alias {attempted_alias}")


dist_cache: dict[tuple[str, str], int] = {}


def term_size(t: Term) -> int:
    subterms = t.get_subterms()
    if len(subterms) == 0:
        return 1
    return 1 + sum([term_size(s) for s in subterms])


def term_dist(t1: Term, t2: Term) -> int:
    t1_str = term_to_str(t1)
    t2_str = term_to_str(t2)
    if (t1_str, t2_str) in dist_cache:
        return dist_cache[(t1_str, t2_str)]
    t1_subterms = t1.get_subterms()
    t2_subterms = t2.get_subterms()

    t1_size = term_size(t1)
    t2_size = term_size(t2)

    root_penalty = 0 if t1.get_key() == t2.get_key() else 1
    if len(t1_subterms) == 0:
        return root_penalty + t2_size - 1
    if len(t2_subterms) == 0:
        return root_penalty + t1_size - 1

    t1_whole_dists: list[int] = []
    for t2_sub in t2_subterms:
        sub_size = term_size(t2_sub)
        t1_whole_dists.append(term_dist(t1, t2_sub) + (t2_size - sub_size))

    t2_whole_dists: list[int] = []
    for t1_sub in t1_subterms:
        sub_size = term_size(t1_sub)
        t2_whole_dists.append(term_dist(t1_sub, t2) + (t1_size - sub_size))

    row_subterms = t1_subterms if len(t1_subterms) < len(t2_subterms) else t2_subterms
    col_subterms = t2_subterms if len(t1_subterms) < len(t2_subterms) else t1_subterms
    row_dists: list[list[int]] = []
    for row_sub in row_subterms:
        col_dists: list[int] = []
        for col_sub in col_subterms:
            col_dists.append(term_dist(row_sub, col_sub))
        row_dists.append(col_dists)

    max_size = max(t1_size, t2_size)
    selected_dists: list[int] = []
    orig_num_rows = len(row_dists)
    broke_order = False
    cols_used: set[int] = set()
    for _ in range(orig_num_rows):
        arg_min: tuple[int, int] = (-1, -1)
        min_dist = max_size
        for i in range(len(row_dists)):
            for j in range(len(row_dists[0])):
                if row_dists[i][j] < min_dist:
                    min_dist = row_dists[i][j]
                    arg_min = i, j
        selected_dists.append(min_dist)
        pop_row, pop_col = arg_min
        if pop_row != 0:
            broke_order = True
        row_dists.pop(pop_row)
        row_dists = [r[:pop_col] + r[(pop_col + 1) :] for r in row_dists]
        cols_used.add(pop_col)
    cols_unused = set(range(len(col_subterms))) - cols_used
    col_penalty = sum([term_size(col_subterms[i]) for i in cols_unused])
    order_penalty = 1 if broke_order else 0
    print(order_penalty)
    unif_dist = order_penalty + root_penalty + sum(selected_dists) + col_penalty

    t1_whole_dist = min(t1_whole_dists)
    t2_whole_dist = min(t2_whole_dists)

    result = min(t1_whole_dist, t2_whole_dist, unif_dist)
    dist_cache[(t1_str, t2_str)] = result
    return result
