from __future__ import annotations
from typing import Any, Optional
from dataclasses import dataclass
from typeguard import typechecked
import json
import ipdb
import functools
from edist import ted, seted, sed


import numpy as np
import numpy.typing as npt

from util.util import get_basic_logger

_logger = get_basic_logger(__name__)


@typechecked
class Name:
    def __init__(self, id: str) -> None:
        self.id = id

    def to_json(self) -> Any:
        return {"id": self.id}

    def to_strtree(self) -> StrTree:
        return StrTree(f"name: {self.id}", [])

    @classmethod
    def from_json(cls, json_data: Any) -> Name:
        return cls(json_data["id"])

    @classmethod
    def from_id_ast(cls, ast: Any) -> Name:
        assert isinstance(ast, dict)
        ast_list = ast["v"]
        assert ast_list[0] == "Id"
        return cls(ast_list[1])

    @classmethod
    def from_ast(cls, ast: Any) -> Name:
        assert isinstance(ast, dict)
        name_list = ast["v"]
        if name_list[0] == "Name":
            return cls(name_list[1][1])
        if name_list[0] == "Anonymous":
            return cls("_")
        raise ValueError(f"Unexpected Name in {ast}")


@typechecked
class StringT:
    def __init__(self, val: str) -> None:
        self.val = val

    def to_strtree(self) -> StrTree:
        return StrTree(f"str: {self.val}", [])

    def to_json(self) -> Any:
        return {"val": self.val}

    @classmethod
    def from_json(cls, json_data: Any) -> StringT:
        return cls(json_data["val"])

    @classmethod
    def from_ast(cls, ast: Any) -> StringT:
        assert isinstance(ast, list)
        assert ast[0] == "String"
        return cls(ast[1])


@typechecked
class NumberT:
    def __init__(self, num: str, frac: str, exp: str) -> None:
        self.num = num
        self.frac = frac
        self.exp = exp

    def to_strtree(self) -> StrTree:
        return StrTree(f"num: {self.num}; {self.frac}; {self.exp}", [])

    def to_json(self) -> Any:
        return {
            "num": self.num,
            "frac": self.frac,
            "exp": self.exp,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> NumberT:
        return cls(json_data["num"], json_data["frac"], json_data["exp"])

    @classmethod
    def from_ast(cls, ast: Any) -> NumberT:
        try:
            assert ast[0] == "Number"
        except:
            pass
            # ipdb.set_trace()
        assert ast[1][0] == ["SPlus"]
        return cls(ast[1][1]["int"], ast[1][1]["frac"], ast[1][1]["exp"])


PrimT = StringT | NumberT


def prim_to_json(prim: PrimT) -> Any:
    return {"prim_name": prim.__class__.__name__} | prim.to_json()


def prim_from_json(json_data: Any) -> PrimT:
    attempted_name = json_data["prim_name"]
    match attempted_name:
        case StringT.__name__:
            return StringT.from_json(json_data)
        case NumberT.__name__:
            return NumberT.from_json(json_data)
        case _:
            raise ValueError(f"Unrecognized primitive: {attempted_name}")


def prim_from_ast(ast: Any) -> PrimT:
    assert isinstance(ast, list)
    assert ast[0] == "CPrim"
    match ast[1][0]:
        case "Number":
            return NumberT.from_ast(ast[1])
        case "String":
            return StringT.from_ast(ast[1])
        case _:
            raise ValueError(f"unrecognized primative: {ast[1][0]}")


@typechecked
class QualIdT:
    def __init__(self, quals: list[str], id: str) -> None:
        self.quals = quals
        self.id = id

    def to_string(self) -> str:
        return ".".join(self.quals + [self.id])

    def to_strtree(self) -> StrTree:
        return StrTree(f"qual: {self.to_string()}", [])

    def to_json(self) -> Any:
        return {
            "quals": self.quals,
            "id": self.id,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> QualIdT:
        return cls(json_data["quals"], json_data["id"])

    @classmethod
    def from_ast_qual(cls, ast: Any) -> QualIdT:
        assert isinstance(ast, dict)
        ast_list = ast["v"]
        assert len(ast_list) == 3
        assert ast_list[0] == "Ser_Qualid"
        assert ast_list[1][0] == "DirPath"
        dir_list = [d[1] for d in ast_list[1][1]]
        assert ast_list[2][0] == "Id"
        id = ast_list[2][1]
        try:
            return cls(dir_list, id)
        except:
            pass
            # ipdb.set_trace()

    @classmethod
    def from_ast_ref(cls, ast: Any) -> QualIdT:
        assert isinstance(ast, list)
        assert len(ast) == 3
        assert ast[0] == "CRef"
        return cls.from_ast_qual(ast[1])


@typechecked
class Binder:
    def __init__(self, names: list[Name], ty: Term) -> None:
        self.names = names
        self.ty = ty

    def to_strtree(self) -> StrTree:
        name = ", ".join([n.id for n in self.names])
        return StrTree(f"binder: {name}", [self.ty.to_strtree()])

    def to_json(self) -> Any:
        return {"names": [n.to_json() for n in self.names], "ty": term_to_json(self.ty)}

    @classmethod
    def from_json(cls, json_data: Any) -> Binder:
        names = [Name.from_json(n) for n in json_data["names"]]
        ty = term_from_json(json_data["ty"])
        return cls(names, ty)

    @classmethod
    def from_ast(cls, ast: Any) -> Binder:
        assert isinstance(ast, list)
        assert len(ast) == 4
        assert ast[0] == "CLocalAssum"
        names = [Name.from_ast(n) for n in ast[1]]
        ty = term_from_ast(ast[3])
        return cls(names, ty)


@typechecked
class FunT:
    def __init__(self, binders: list[Binder], body: Term) -> None:
        self.binders = binders
        self.body = body

    def to_strtree(self) -> StrTree:
        return StrTree(
            "forall", [b.to_strtree() for b in self.binders] + [self.body.to_strtree()]
        )

    def to_json(self) -> Any:
        return {
            "binders": [b.to_json() for b in self.binders],
            "body": term_to_json(self.body),
        }

    @classmethod
    def from_json(cls, json_data: Any) -> FunT:
        binders = [Binder.from_json(b) for b in json_data["binders"]]
        body = term_from_json(json_data["body"])
        return cls(binders, body)

    @classmethod
    def from_ast(cls, ast: Any) -> FunT:
        assert isinstance(ast, list)
        assert ast[0] == "CLambdaN"
        assert len(ast) == 3

        raw_binders = ast[1]
        binders = [Binder.from_ast(b) for b in raw_binders]
        body = term_from_ast(ast[2])
        return cls(binders, body)


@typechecked
class ProdT:
    def __init__(self, binders: list[Binder], body: Term) -> None:
        self.binders = binders
        self.body = body

    def to_strtree(self) -> StrTree:
        return StrTree(
            "forall", [b.to_strtree() for b in self.binders] + [self.body.to_strtree()]
        )

    def to_json(self) -> Any:
        return {
            "binders": [b.to_json() for b in self.binders],
            "body": term_to_json(self.body),
        }

    @classmethod
    def from_json(cls, json_data: Any) -> ProdT:
        binders = [Binder.from_json(b) for b in json_data["binders"]]
        body = term_from_json(json_data["body"])
        return cls(binders, body)

    @classmethod
    def from_ast(cls, ast: Any) -> ProdT:
        assert isinstance(ast, list)
        assert ast[0] == "CProdN"
        assert len(ast) == 3

        raw_binders = ast[1]
        binders = [Binder.from_ast(b) for b in raw_binders]
        body = term_from_ast(ast[2])
        return cls(binders, body)


@typechecked
class PatCAlias:
    def __init__(self, pattern: Pattern, name: Name) -> None:
        self.pattern = pattern
        self.name = name

    def to_strtree(self) -> StrTree:
        name = f"alias {self.name}"
        return StrTree(name, [self.pattern.to_strtree()])

    def to_json(self) -> Any:
        return {
            "pattern": pattern_to_json(self.pattern),
            "name": self.name.to_json(),
        }

    @classmethod
    def from_json(cls, json_data: Any) -> PatCAlias:
        pattern = pattern_from_json(json_data["pattern"])
        name = Name.from_json(json_data["name"])
        return cls(pattern, name)

    @classmethod
    def from_ast(cls, ast: Any) -> PatCAlias:
        assert isinstance(ast, list)
        assert len(ast) == 3
        assert ast[0] == "CPatAlias"
        pattern = pattern_from_ast(ast[1])
        name = Name.from_ast(ast[2])
        return cls(pattern, name)


@typechecked
class PatCstr:
    def __init__(self, first: QualIdT, rest: list[Pattern]) -> None:
        self.first = first
        self.rest = rest

    def to_json(self) -> Any:
        return {
            "first": self.first.to_json(),
            "rest": [r.to_json() for r in self.rest],
        }

    def to_strtree(self) -> Any:
        name = f"cstr: {self.first.to_string()}"
        return StrTree(name, [r.to_strtree() for r in self.rest])

    @classmethod
    def from_json(cls, json_data: Any) -> PatCstr:
        first = QualIdT.from_json(json_data["first"])
        rest = [pattern_from_json(d) for d in json_data["rest"]]
        return cls(first, rest)

    @classmethod
    def from_ast(cls, ast: Any) -> PatCstr:
        assert isinstance(ast, list)
        assert ast[0] == "CPatCstr"
        first = QualIdT.from_ast_qual(ast[1])
        rest = [pattern_from_ast(a) for a in ast[3]]
        return cls(first, rest)


@typechecked
class PatAtom:
    def __init__(self, val: Optional[QualIdT]):
        self.val = val

    def to_json(self) -> Any:
        return {"val": self.val.to_json() if self.val else None}

    def to_strtree(self) -> StrTree:
        name = self.val.to_string() if self.val else "_"
        return StrTree(f"Pat {name}", [])

    @classmethod
    def from_json(cls, json_data: Any) -> Any:
        return cls(QualIdT.from_json(json_data["val"]))

    @classmethod
    def from_ast(cls, ast: Any) -> PatAtom:
        assert isinstance(ast, list)
        assert ast[0] == "CPatAtom"
        qualid = QualIdT.from_ast_qual(ast[1]) if ast[1] else None
        return cls(qualid)


@typechecked
class PatPrim:
    def __init__(self, val: PrimT) -> None:
        self.val = val

    def to_strtree(self) -> StrTree:
        val_strtree = self.val.to_strtree()
        return StrTree(f"Pat {val_strtree.key}", [])

    def to_json(self) -> Any:
        return {"val": prim_to_json(self.val)}

    @classmethod
    def from_json(cls, json_data: Any) -> PatPrim:
        return cls(NumberT.from_json(json_data["val"]))

    @classmethod
    def from_ast(cls, ast: Any) -> PatPrim:
        assert isinstance(ast, list)
        assert ast[0] == "CPatPrim"
        match ast[1][0]:
            case "Number":
                return cls(NumberT.from_ast(ast[1]))
            case "String":
                return cls(StringT.from_ast(ast[1]))
            case _:
                raise ValueError(f"Unrecognized prim: {ast[1]}")


Pattern = PatCstr | PatAtom | PatPrim | PatCAlias


def pattern_to_json(pattern: Pattern) -> Any:
    return {"type_name": pattern.__class__.__name__} | pattern.to_json()


def pattern_from_json(json_data: Any) -> Pattern:
    attempted_name = json_data["type_name"]
    match attempted_name:
        case PatCstr.__name__:
            return PatCstr.from_json(json_data)
        case PatAtom.__name__:
            return PatAtom.from_json(json_data)
        case PatCAlias.__name__:
            return PatCAlias.from_json(json_data)
        case PatPrim.__name__:
            return PatPrim.from_json(json_data)
        case _:
            raise ValueError(f"Unknown pattern type: {attempted_name}")


def pattern_from_ast(ast: Any) -> Pattern:
    assert isinstance(ast, dict)
    ast_list = ast["v"]
    match ast_list[0]:
        case "CPatCstr":
            return PatCstr.from_ast(ast_list)
        case "CPatAtom":
            return PatAtom.from_ast(ast_list)
        case "CPatAlias":
            return PatCAlias.from_ast(ast_list)
        case "CPatPrim":
            return PatPrim.from_ast(ast_list)
        case "CPatDelimiters":
            # %positive and %negative stuff
            return pattern_from_ast(ast_list[2])
        case _:
            raise ValueError(f"Unknown pattern: {ast_list[0]}")


@typechecked
class MatchCase:
    def __init__(
        self, term: Term, name: Optional[Name], pattern: Optional[Pattern]
    ) -> None:
        self.term = term
        self.name = name
        self.pattern = pattern

    def to_strtree(self) -> StrTree:
        return StrTree("case", [self.term.to_strtree()])

    def to_json(self) -> Any:
        return {
            "term": term_to_json(self.term),
            "name": self.name.to_json() if self.name else None,
            "pattern": pattern_to_json(self.pattern) if self.pattern else None,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> MatchCase:
        term = term_from_json(json_data["term"])
        name = Name.from_json(json_data["name"]) if json_data["name"] else None
        pattern = (
            pattern_from_json(json_data["pattern"]) if json_data["pattern"] else None
        )
        return cls(term, name, pattern)

    @classmethod
    def from_ast(cls, ast: Any) -> MatchCase:
        assert isinstance(ast, list)
        assert len(ast) == 3
        term = term_from_ast(ast[0])
        name = Name.from_ast(ast[1]) if ast[1] else None
        pattern = pattern_from_ast(ast[2]) if ast[2] else None
        return cls(term, name, pattern)


@typechecked
class MatchBranch:
    def __init__(self, lhs: list[list[Pattern]], rhs: Term) -> None:
        self.lhs = lhs
        self.rhs = rhs

    def to_strtree(self) -> StrTree:
        flat_patterns = [p for d in self.lhs for p in d]
        return StrTree("MatchBranch", [p.to_strtree() for p in flat_patterns])

    def to_json(self) -> Any:
        return {
            "lhs": [[pattern_to_json(c) for c in d] for d in self.lhs],
            "rhs": term_to_json(self.rhs),
        }

    @classmethod
    def from_json(cls, json_data: Any) -> MatchBranch:
        lhs = [[pattern_from_json(c) for c in d] for d in json_data["lhs"]]
        rhs = term_from_json(json_data["rhs"])
        return cls(lhs, rhs)

    @classmethod
    def from_ast(cls, ast: Any) -> MatchBranch:
        assert isinstance(ast, dict)
        ast_list = ast["v"]
        lhs = [[pattern_from_ast(c) for c in d] for d in ast_list[0]]
        rhs = term_from_ast(ast_list[1])
        return cls(lhs, rhs)


class MatchT:
    def __init__(
        self,
        return_item: Optional[Term],
        cases: list[MatchCase],
        branches: list[MatchBranch],
    ) -> None:
        self.return_item = return_item
        self.cases = cases
        self.branches = branches

    def to_strtree(self) -> StrTree:
        return StrTree(
            "match",
            [c.to_strtree() for c in self.cases]
            + [b.to_strtree() for b in self.branches],
        )

    def to_json(self) -> Any:
        return {
            "return_item": term_to_json(self.return_item) if self.return_item else None,
            "cases": [c.to_json() for c in self.cases],
            "branches": [b.to_json() for b in self.branches],
        }

    @classmethod
    def from_json(cls, json_data: Any) -> MatchT:
        return_item = (
            term_from_json(json_data["return_item"])
            if json_data["return_item"]
            else None
        )
        cases = [MatchCase.from_json(c) for c in json_data["cases"]]
        branches = [MatchBranch.from_json(b) for b in json_data["branches"]]
        return cls(return_item, cases, branches)

    @classmethod
    def from_ast(cls, ast: Any) -> MatchT:
        assert isinstance(ast, list)
        assert len(ast) == 5
        assert ast[0] == "CCases"
        return_item = term_from_ast(ast[2]) if ast[2] else None
        cases = [MatchCase.from_ast(t) for t in ast[3]]
        branches = [MatchBranch.from_ast(t) for t in ast[4]]
        return cls(return_item, cases, branches)


class CoFixDecl:
    def __init__(
        self, name: Name, binders: list[Binder], ret_type: Term, body: Term
    ) -> None:
        self.name = name
        self.binders = binders
        self.ret_type = ret_type
        self.body = body

    def to_strtree(self) -> StrTree:
        return StrTree(
            f"fix {self.name.id}",
            [b.to_strtree() for b in self.binders]
            + [self.ret_type.to_strtree(), self.body.to_strtree()],
        )

    def to_json(self) -> Any:
        return {
            "name": self.name.to_json(),
            "binders": [b.to_json() for b in self.binders],
            "ret_type": term_to_json(self.ret_type),
            "body": term_to_json(self.body),
        }

    @classmethod
    def from_json(cls, json_data: Any) -> CoFixDecl:
        name = Name.from_json(json_data["name"])
        binders = [Binder.from_json(b) for b in json_data["binders"]]
        ret_type = term_from_json(json_data["ret_type"])
        body = term_from_json(json_data["body"])
        return cls(name, binders, ret_type, body)

    @classmethod
    def from_ast(cls, ast: Any) -> CoFixDecl:
        assert isinstance(ast, list)
        name = Name.from_id_ast(ast[0])
        binders = [Binder.from_ast(b) for b in ast[1]]
        ret_type = term_from_ast(ast[2])
        body = term_from_ast(ast[3])
        return cls(name, binders, ret_type, body)


class FixDecl:
    def __init__(
        self, name: Name, binders: list[Binder], ret_type: Term, body: Term
    ) -> None:
        self.name = name
        self.binders = binders
        self.ret_type = ret_type
        self.body = body

    def to_strtree(self) -> StrTree:
        return StrTree(
            f"fix {self.name.id}",
            [b.to_strtree() for b in self.binders]
            + [self.ret_type.to_strtree(), self.body.to_strtree()],
        )

    def to_json(self) -> Any:
        return {
            "name": self.name.to_json(),
            "binders": [b.to_json() for b in self.binders],
            "ret_type": term_to_json(self.ret_type),
            "body": term_to_json(self.body),
        }

    @classmethod
    def from_json(cls, json_data: Any) -> FixDecl:
        name = Name.from_json(json_data["name"])
        binders = [Binder.from_json(b) for b in json_data["binders"]]
        ret_type = term_from_json(json_data["ret_type"])
        body = term_from_json(json_data["body"])
        return cls(name, binders, ret_type, body)

    @classmethod
    def from_ast(cls, ast: Any) -> FixDecl:
        assert isinstance(ast, list)
        name = Name.from_id_ast(ast[0])
        binders = [Binder.from_ast(b) for b in ast[2]]
        ret_type = term_from_ast(ast[3])
        body = term_from_ast(ast[4])
        return cls(name, binders, ret_type, body)


class FixT:
    def __init__(self, decls: list[FixDecl]) -> None:
        self.decls = decls

    def to_json(self) -> Any:
        return {"decls": [d.to_json() for d in self.decls]}

    def to_strtree(self) -> StrTree:
        return StrTree("fix", [d.to_strtree() for d in self.decls])

    @classmethod
    def from_json(cls, json_data: Any) -> FixT:
        decls = [FixDecl.from_json(d) for d in json_data["decls"]]
        return cls(decls)

    @classmethod
    def from_ast(cls, ast: Any) -> FixT:
        assert isinstance(ast, list)
        assert ast[0] == "CFix"
        decls = [FixDecl.from_ast(a) for a in ast[2]]
        return cls(decls)


class CoFixT:
    def __init__(self, decls: list[CoFixDecl]) -> None:
        self.decls = decls

    def to_json(self) -> Any:
        return {"decls": [d.to_json() for d in self.decls]}

    def to_strtree(self) -> StrTree:
        return StrTree("fix", [d.to_strtree() for d in self.decls])

    @classmethod
    def from_json(cls, json_data: Any) -> CoFixT:
        decls = [FixDecl.from_json(d) for d in json_data["decls"]]
        return cls(decls)

    @classmethod
    def from_ast(cls, ast: Any) -> CoFixT:
        assert isinstance(ast, list)
        assert ast[0] == "CCoFix"
        decls = [CoFixDecl.from_ast(a) for a in ast[2]]
        return cls(decls)


class AppT:
    def __init__(self, fn: Term, args: list[Term]) -> None:
        self.fn = fn
        self.args = args

    def to_strtree(self) -> StrTree:
        return StrTree(
            "appt", [self.fn.to_strtree()] + [a.to_strtree() for a in self.args]
        )

    def to_json(self) -> Any:
        return {
            "fn": term_to_json(self.fn),
            "args": [term_to_json(a) for a in self.args],
        }

    @classmethod
    def from_json(cls, json_data: Any) -> AppT:
        fn = term_from_json(json_data["fn"])
        args = [term_from_json(a) for a in json_data["args"]]
        return cls(fn, args)

    @classmethod
    def from_expl_ast(cls, ast: Any) -> AppT:
        assert isinstance(ast, list)
        assert ast[0] == "CAppExpl"
        fn = QualIdT.from_ast_qual(ast[1][0])
        args = [term_from_ast(a) for a in ast[2]]
        return cls(fn, args)

    @classmethod
    def from_ast(cls, ast: Any) -> AppT:
        assert isinstance(ast, list)
        assert ast[0] == "CApp"
        fn = term_from_ast(ast[1])
        args = [term_from_ast(a[0]) for a in ast[2]]
        return cls(fn, args)


class LetTupleT:
    def __init__(self, ids: list[Name], unpack: Term, body: Term) -> None:
        self.ids = ids
        self.unpack = unpack
        self.body = body

    def to_strtree(self) -> StrTree:
        joined_names = ", ".join([n.id for n in self.ids])
        return StrTree(
            f"let tuple: {joined_names}",
            [self.unpack.to_strtree(), self.body.to_strtree()],
        )

    def to_json(self) -> Any:
        return {
            "ids": [i.to_json() for i in self.ids],
            "unpack": term_to_json(self.unpack),
            "body": term_to_json(self.body),
        }

    @classmethod
    def from_json(cls, json_data: Any) -> LetTupleT:
        ids = [Name.from_json(i) for i in json_data["ids"]]
        unpack = term_from_json(json_data["unpack"])
        body = term_from_json(json_data["body"])
        return cls(ids, unpack, body)

    @classmethod
    def from_ast(cls, ast: Any) -> LetTupleT:
        assert isinstance(ast, list)
        assert len(ast) == 5
        assert ast[0] == "CLetTuple"
        names = [Name.from_ast(n) for n in ast[1]]
        unpack = term_from_ast(ast[3])
        body = term_from_ast(ast[4])
        return cls(names, unpack, body)


class IfT:
    def __init__(self, guard: Term, then_branch: Term, else_branch: Term) -> None:
        self.guard = guard
        self.then_branch = then_branch
        self.else_branch = else_branch

    def to_strtree(self) -> StrTree:
        return StrTree(
            "if",
            [
                self.guard.to_strtree(),
                self.then_branch.to_strtree(),
                self.else_branch.to_strtree(),
            ],
        )

    def to_json(self) -> Any:
        return {
            "guard": term_to_json(self.guard),
            "then_branch": term_to_json(self.then_branch),
            "else_branch": term_to_json(self.else_branch),
        }

    @classmethod
    def from_json(cls, json_data: Any) -> IfT:
        guard = term_from_json(json_data["guard"])
        then_branch = term_from_json(json_data["then_branch"])
        else_branch = term_from_json(json_data["else_branch"])
        return cls(guard, then_branch, else_branch)

    @classmethod
    def from_ast(cls, ast: Any) -> IfT:
        assert isinstance(ast, list)
        assert ast[0] == "CIf"
        guard = term_from_ast(ast[1])
        then_branch = term_from_ast(ast[3])
        else_branch = term_from_ast(ast[4])
        return cls(guard, then_branch, else_branch)


@typechecked
class SortT:
    def __init__(self, sort_name: str) -> None:
        self.sort_name = sort_name

    def to_json(self) -> Any:
        return {"sort_name": self.sort_name}

    def to_strtree(self) -> StrTree:
        return StrTree(f"sort: {self.sort_name}", [])

    @classmethod
    def from_json(cls, json_data: Any) -> SortT:
        return cls(json_data["sort_name"])

    @classmethod
    def from_ast(cls, ast: Any) -> SortT:
        assert isinstance(ast, list)
        assert ast[0] == "CSort"
        if ast[1][0] == "UNamed":
            name = ast[1][1][1][0][0][0]
            return cls(name)
        elif ast[1][0] == "UAnonymous":
            return cls("CType")
        else:
            raise ValueError(f"Unknown sort name: {ast[1][0]}")


class RecordT:
    def __init__(self, terms: list[tuple[QualIdT, Term]]) -> None:
        self.terms = terms

    def to_strtree(self) -> StrTree:
        sub_strtrees: list[StrTree] = []
        for qual, term in self.terms:
            sub_strtrees.append(qual.to_strtree())
            sub_strtrees.append(term.to_strtree())
        return StrTree("record", sub_strtrees)

    def to_json(self) -> Any:
        return {
            "terms": [
                {"qual": term_to_json(q), "term": term_to_json(t)}
                for q, t in self.terms
            ]
        }

    @classmethod
    def from_json(cls, json_data: Any) -> RecordT:
        terms: list[tuple[QualIdT, Term]] = []
        for term_dict in json_data["terms"]:
            terms.append((term_dict["qual"], term_dict["term"]))
        return cls(terms)

    @classmethod
    def from_ast(cls, ast: Any) -> RecordT:
        assert type(ast) == list
        assert ast[0] == "CRecord"
        terms: list[tuple[QualIdT, Term]] = []
        for binding in ast[1]:
            terms.append((QualIdT.from_ast_qual(binding[0]), term_from_ast(binding[1])))
        return cls(terms)


class EvarT:
    def __init__(self, id: Name, terms: list[tuple[Name, Term]]) -> None:
        self.id = id
        self.terms = terms

    def to_strtree(self) -> StrTree:
        key = f"evar: {self.id.id}"
        children: list[StrTree] = []
        for name, term in self.terms:
            children.append(name.to_strtree())
            children.append(term.to_strtree())
        return StrTree(key, children)

    def to_json(self) -> Any:
        return {
            "id": self.id,
            "terms": [{"name": n, "term": t} for n, t in self.terms],
        }

    @classmethod
    def from_json(cls, json_data: Any) -> EvarT:
        id = json_data["id"]
        terms = [(j["name"], j["term"]) for j in json_data["terms"]]
        return cls(id, terms)

    @classmethod
    def from_ast(cls, ast: Any) -> EvarT:
        assert isinstance(ast, list)
        assert ast[0] == "CEvar"
        assert len(ast) == 3
        id = Name.from_id_ast(ast[1])
        terms: list[tuple[Name, Term]] = []
        for t_list in ast[2]:
            name = Name.from_id_ast(t_list[0])
            term = term_from_ast(t_list[1])
            terms.append((name, term))
        return cls(id, terms)


class NotationT:
    def __init__(self, terms: list[Term]) -> None:
        self.terms = terms

    def to_strtree(self) -> StrTree:
        return StrTree("notation", [t.to_strtree() for t in self.terms])

    def to_json(self) -> Any:
        return {"terms": [term_to_json(t) for t in self.terms]}

    @classmethod
    def from_json(cls, json_data: Any) -> NotationT:
        terms = [term_from_json(t) for t in json_data["terms"]]
        return cls(terms)

    @classmethod
    def from_ast(cls, ast: Any) -> NotationT:
        assert isinstance(ast, list)
        assert len(ast) == 4
        assert ast[0] == "CNotation"
        terms = [term_from_ast(t) for t in ast[3][0]]
        return cls(terms)


class HoleT:
    def __init__(self) -> None:
        pass

    def to_strtree(self) -> StrTree:
        return StrTree("hole", [])

    def to_json(self) -> Any:
        return {}

    @classmethod
    def from_json(cls, json_data: Any) -> HoleT:
        return cls()

    @classmethod
    def from_ast(cls, ast: Any) -> HoleT:
        assert isinstance(ast, list)
        assert ast[0] == "CHole"
        return cls()


class UnknownT:
    def __init__(self) -> None:
        pass

    def to_json(self) -> Any:
        return {}

    def to_strtree(self) -> Any:
        return StrTree("unknown", [])

    @classmethod
    def from_json(cls, json_data: Any) -> UnknownT:
        return cls()


Term = (
    FunT
    | ProdT
    | QualIdT
    | PrimT
    | MatchT
    | FixT
    | CoFixT
    | AppT
    | LetTupleT
    | IfT
    | SortT
    | RecordT
    | EvarT
    | HoleT
    | NotationT
    | UnknownT
)


def term_from_ast(ast: Any) -> Term:
    assert isinstance(ast, dict)
    term = ast["v"]
    match term[0]:
        case "CLambdaN":
            return FunT.from_ast(term)
        case "CRef":
            return QualIdT.from_ast_ref(term)
        case "CProdN":
            return ProdT.from_ast(term)
        case "CPrim":
            return prim_from_ast(term)
        case "CCases":
            return MatchT.from_ast(term)
        case "CFix":
            return FixT.from_ast(term)
        case "CApp":
            return AppT.from_ast(term)
        case "CLetTuple":
            return LetTupleT.from_ast(term)
        case "CIf":
            return IfT.from_ast(term)
        case "CSort":
            return SortT.from_ast(term)
        case "CRecord":
            return RecordT.from_ast(term)
        case "CDelimiters":
            return term_from_ast(term[2])
        case "CCoFix":
            return CoFixT.from_ast(term)
        case "CEvar":
            return EvarT.from_ast(term)
        case "CHole":
            return HoleT.from_ast(term)
        case "CNotation":
            return NotationT.from_ast(term)
        case "CAppExpl":
            return AppT.from_expl_ast(term)
        case _:
            term_size = len(json.dumps(ast))
            raise ValueError(f"Unhandled Term Type: {term[0]} of size {term_size}")
            _logger.warning(
                f"Unhandled Term Type: {term[0]} of size {term_size}. Inserting unknown tree."
            )
            return UnknownT()


class AdjTree:
    def __init__(self, nodes: list[str], idxs: list[list[int]]):
        self.nodes = nodes
        self.idxs = idxs
    
    def distance(self, other: AdjTree) -> int:
        return ted.standard_ted(self.nodes, self.idxs, other.nodes, other.idxs)
    
    def fast_distance(self, other: AdjTree) -> int:
        return seted.standard_seted(self.nodes, other.nodes)
    
    @functools.cache
    def get_node_multiset(self) -> list[str]:
        return sorted(self.nodes)
    
    def custom_set_dist(self, other: AdjTree) -> int:
        return sed.standard_sed(self.get_node_multiset(), other.get_node_multiset())

    
    @classmethod
    @functools.cache
    def __from_stree(cls, t: StrTree, start_idx: int) -> tuple[AdjTree, int]:
        nodes = [t.key]
        idxs: list[int] = []
        child_idxs: list[list[int]] = [idxs]
        next_idx = start_idx + 1
        for c in t.children: 
            idxs.append(next_idx)
            c_adj_tree, next_idx = AdjTree.__from_stree(c, next_idx)
            nodes.extend(c_adj_tree.nodes)
            child_idxs.extend(c_adj_tree.idxs)
        return cls(nodes, child_idxs), next_idx


    @classmethod
    def from_stree(cls, t: StrTree) -> AdjTree:
        adj_t, _ = cls.__from_stree(t, 0)
        return adj_t 
    

class StrTree:
    def __init__(self, key: str, children: list[StrTree]) -> None:
        self.key = key
        self.children = children
        self.__cached_hash: Optional[int] = None
        self.__cached_size: Optional[int] = None
        self.__cached_dists: dict[tuple[StrTree, Optional[int]], tuple[int, int]] = {}
        self.__cached_keyset: Optional[list[str]] = None

    def __hash__(self) -> int:
        if self.__cached_hash:
            return self.__cached_hash
        child_hash = hash(tuple([hash(c) for c in self.children]))
        my_hash = hash((f"cstr: {self.key}", child_hash))
        self.__cached_hash = my_hash
        return my_hash

    def has_unknown(self) -> bool:
        return self.key == "unknown" or any([c.has_unknown() for c in self.children])

    def to_string(self, indent: str = "") -> str:
        s = f"{indent}{self.key}\n"
        child_str = ""
        for child in self.children:
            child_str += child.to_string(indent=indent + "  ")
        return s + child_str

    def distance(
        self,
        other: StrTree,
        incurred_distance: int = 0,
        abort_at_distance: Optional[int] = None,
        heuristic_depth: Optional[int] = None,
    ) -> int:
        if heuristic_depth == 0:
            return self.keyset_compare(other, abort_at_distance=abort_at_distance)
        if abort_at_distance is not None:
            heuristic1 = abs(self.size() - other.size())
            if abort_at_distance <= (incurred_distance + heuristic1):
                return abort_at_distance
            heuristic2 = self.keyset_compare(other, abort_at_distance)
            if abort_at_distance <= (incurred_distance + heuristic2):
                return abort_at_distance
            # if abort_at_distance <= self.keyset_compare(other, abort_at_distance):
            #     return abort_at_distance
            # if abort_at_distance <= abs(self.size() - other.size()):
            #     return abort_at_distance
        else:
            abort_at_distance = self.size() + other.size()

        next_heuristic_depth = (
            heuristic_depth - 1 if heuristic_depth is not None else None
        )

        orig_abort_dist = abort_at_distance
        if (other, heuristic_depth) in self.__cached_dists:
            cached_dist, cached_abort_dist = self.__cached_dists[
                (other, heuristic_depth)
            ]
            if abort_at_distance <= cached_abort_dist:
                return cached_dist

        root_penalty = 0 if self.key == other.key else 1
        if len(self.children) == 0:
            distance = other.size() - (1 - root_penalty)
            self.__cached_dists[(other, heuristic_depth)] = distance, orig_abort_dist
            return distance
        if len(other.children) == 0:
            distance = self.size() - (1 - root_penalty)
            self.__cached_dists[(other, heuristic_depth)] = distance, orig_abort_dist
            return distance

        # Child Matching
        num_rows = len(self.children)
        num_cols = len(other.children)
        if num_rows <= num_cols:
            num_unmatched_rows = num_rows - num_cols
            matching_lb_penalty = sum(
                sorted([r.size() for r in self.children])[:num_unmatched_rows]
            )
        else:
            num_unmatched_cols = num_cols - num_rows
            matching_lb_penalty = sum(
                sorted([r.size() for r in other.children])[:num_unmatched_cols]
            )

        distances: npt.NDArray[int] = np.full((num_rows, num_cols), 0)
        for i, ci in enumerate(self.children):
            for j, cj in enumerate(other.children):
                distances[i][j] = ci.distance(
                    cj,
                    incurred_distance + matching_lb_penalty + root_penalty,
                    abort_at_distance,
                    next_heuristic_depth,
                )

        mask_val = self.size() + other.size()
        num_mins = min(num_rows, num_cols)
        matched_distance = 0
        my_children_matched = [False for _ in self.children]
        other_children_matched = [False for _ in other.children]
        out_of_order = False
        for _ in range(num_mins):
            next_min_flat_idx = distances.argmin()
            next_min_x, next_min_y = np.unravel_index(
                next_min_flat_idx, distances.shape
            )
            matched_distance += int(distances[next_min_x, next_min_y])
            distances[next_min_x, :] = mask_val
            distances[:, next_min_y] = mask_val
            my_children_matched[next_min_x] = True
            other_children_matched[next_min_y] = True
            if next_min_x != next_min_y:
                out_of_order = True

        my_unmatched_penalty = sum(
            [c.size() for c, m in zip(self.children, my_children_matched) if not m]
        )
        other_unmatched_penalty = sum(
            [c.size() for c, m in zip(other.children, other_children_matched) if not m]
        )
        out_of_order_penalty = 1 if out_of_order else 0
        total_match_distance = (
            root_penalty
            + matched_distance
            + out_of_order_penalty
            + my_unmatched_penalty
            + other_unmatched_penalty
        )
        abort_at_distance = min(total_match_distance, abort_at_distance)

        # Pushing
        self_push_other_dists: list[int] = []
        for oc in other.children:
            incurred = other.size() - oc.size()
            dist = (
                self.distance(
                    oc,
                    incurred_distance + incurred,
                    abort_at_distance,
                    next_heuristic_depth,
                )
                + incurred
            )
            self_push_other_dists.append(dist)
            abort_at_distance = min(dist, abort_at_distance)

        other_push_self_dists: list[int] = []
        for c in self.children:
            incurred = self.size() - c.size()
            dist = (
                c.distance(
                    other,
                    incurred_distance + incurred,
                    abort_at_distance,
                    next_heuristic_depth,
                )
                + incurred
            )
            other_push_self_dists.append(dist)
            abort_at_distance = min(dist, abort_at_distance)

        distance = abort_at_distance
        self.__cached_dists[(other, heuristic_depth)] = distance, orig_abort_dist
        return distance

    def to_json(self) -> Any:
        return {
            "key": self.key,
            "children": [c.to_json() for c in self.children],
        }

    def size(self) -> int:
        if self.__cached_size is not None:
            return self.__cached_size
        size = 1 + sum([c.size() for c in self.children])
        self.__cached_size = size
        return size

    def keyset_compare(
        self, other: StrTree, abort_at_distance: Optional[int] = None
    ) -> int:
        # Underapproximation of tree edit distance
        my_keyset = self.keyset()
        other_keyset = other.keyset()
        my_ptr = 0
        other_ptr = 0
        distance = 0
        while my_ptr < len(my_keyset) and other_ptr < len(other_keyset):
            if my_keyset[my_ptr] == other_keyset[other_ptr]:
                my_ptr += 1
                other_ptr += 1
            elif my_keyset[my_ptr] < other_keyset[other_ptr]:
                my_ptr += 1
                distance += 1
                if abort_at_distance and abort_at_distance <= distance:
                    return abort_at_distance
            else:
                other_ptr += 1
                distance += 1
                if abort_at_distance and abort_at_distance <= distance:
                    return abort_at_distance
        return distance + (len(my_keyset) - my_ptr) + (len(other_keyset) - other_ptr)

    def keyset(self) -> list[str]:
        if self.__cached_keyset is not None:
            return self.__cached_keyset
        else:
            keyset: list[str] = []
            # Room for optimization
            for c in self.children:
                keyset.extend(c.keyset())
            keyset.append(self.key)
            keyset.sort()
            self.__cached_keyset = keyset
            return keyset
    
    @functools.cache
    def get_breadth_prefix(self, size_limit: int) -> StrTree:
        assert 0 < size_limit
        root_tree = StrTree(self.key, [])
        size_limit -= 1
        worklist = [(c, root_tree) for c in self.children]
        while 0 < len(worklist) and 0 < size_limit:
            new_child, cur_tree = worklist.pop(0)
            new_child_empty = StrTree(new_child.key, [])
            cur_tree.children.append(new_child_empty)
            size_limit -= 1
            worklist.extend([(c, new_child_empty) for c in new_child.children])
        return root_tree 


    @classmethod
    def from_json(cls, json_data: Any) -> StrTree:
        key = json_data["key"]
        children = [cls.from_json(c) for c in json_data["children"]]
        return cls(key, children)


def term_to_json(t: Term) -> Any:
    return {"name": t.__class__.__name__} | t.to_json()


def term_from_json(json_data: Any) -> Term:
    attempted_name = json_data["name"]
    match attempted_name:
        case FunT.__name__:
            return FunT.from_json(json_data)
        case QualIdT.__name__:
            return QualIdT.from_json(json_data)
        case ProdT.__name__:
            return ProdT.from_json(json_data)
        case NumberT.__name__:
            return NumberT.from_json(json_data)
        case StringT.__name__:
            return StringT.from_json(json_data)
        case MatchT.__name__:
            return MatchT.from_json(json_data)
        case FixT.__name__:
            return FixT.from_json(json_data)
        case CoFixT.__name__:
            return CoFixT.from_json(json_data)
        case AppT.__name__:
            return AppT.from_json(json_data)
        case IfT.__name__:
            return IfT.from_json(json_data)
        case RecordT.__name__:
            return RecordT.from_json(json_data)
        case SortT.__name__:
            return SortT.from_json(json_data)
        case EvarT.__name__:
            return EvarT.from_json(json_data)
        case HoleT.__name__:
            return HoleT.from_json(json_data)
        case NotationT.__name__:
            return NotationT.from_json(json_data)
        case _:
            raise ValueError(f"Unrecognized term class {attempted_name}")


def get_body_from_definition(ast: Any) -> Any:
    body = ast["v"]["expr"][1][3]
    assert isinstance(body, list)
    assert body[0] == "DefineBody"
    expr = body[3]
    return expr
