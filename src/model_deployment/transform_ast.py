from __future__ import annotations
from typing import Any, Optional
from dataclasses import dataclass
from typeguard import typechecked
import ipdb


@typechecked
class Name:
    def __init__(self, id: str) -> None:
        self.id = id

    def to_json(self) -> Any:
        return {"id": self.id}

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
        assert name_list[0] == "Name"
        return cls(name_list[1][1])


@typechecked
class NumberT:
    def __init__(self, num: str, frac: str, exp: str) -> None:
        self.num = num
        self.frac = frac
        self.exp = exp

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
    def from_ast_num(cls, ast: Any) -> NumberT:
        assert ast[0] == "Number"
        assert ast[1][0] == ["SPlus"]
        return cls(ast[1][1]["int"], ast[1][1]["frac"], ast[1][1]["exp"])

    @classmethod
    def from_ast(cls, ast: Any) -> NumberT:
        assert isinstance(ast, list)
        assert ast[0] == "CPrim"
        return cls.from_ast_num(ast[1])


@typechecked
class QualIdT:
    def __init__(self, quals: list[str], id: str) -> None:
        self.quals = quals
        self.id = id

    def to_string(self) -> str:
        return ".".join(self.quals + [self.id])

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
        dir_list = ast_list[1][1]
        assert ast_list[2][0] == "Id"
        id = ast_list[2][1]
        return cls(dir_list, id)

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

    @classmethod
    def from_ast(cls, ast: Any) -> PatCAlias:
        assert isinstance(ast, list)
        assert len(ast) == 3
        assert ast[0] == "CPatAlias"
        pattern = pattern_from_ast(ast[1])
        name = Name.from_ast(ast[2])
        return cls(pattern, name)

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

    # TODO CONVERT TO TREES

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
    def __init__(self, val: QualIdT):
        self.val = val

    def to_json(self) -> Any:
        return {"val": self.val.to_json()}

    def to_strtree(self) -> StrTree:
        return StrTree(f"Pat {self.val.to_string()}", [])

    @classmethod
    def from_json(cls, json_data: Any) -> Any:
        return cls(QualIdT.from_json(json_data["val"]))

    @classmethod
    def from_ast(cls, ast: Any) -> PatAtom:
        assert isinstance(ast, list)
        assert ast[0] == "CPatAtom"
        qualid = QualIdT.from_ast_qual(ast[1])
        return cls(qualid)


@typechecked
class PatPrim:
    def __init__(self, val: NumberT) -> None:
        self.val = val

    def to_strtree(self) -> StrTree:
        return StrTree(f"Pat {self.val.num}-{self.val.exp}-{self.val.frac}", [])

    def to_json(self) -> Any:
        return {
            "val": self.val.to_json(),
        }

    @classmethod
    def from_json(cls, json_data: Any) -> PatPrim:
        return cls(NumberT.from_json(json_data["val"]))

    @classmethod
    def from_ast(cls, ast: Any) -> PatPrim:
        assert isinstance(ast, list)
        assert ast[0] == "CPatPrim"
        return cls(NumberT.from_ast_num(ast[1]))


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
    def from_ast(cls, ast: Any) -> AppT:
        assert isinstance(ast, list)
        assert ast[0] == "CApp"
        fn = term_from_ast(ast[1])
        args = [term_from_ast(a[0]) for a in ast[2]]
        return cls(fn, args)


Term = FunT | ProdT | QualIdT | NumberT | MatchT | FixT | AppT


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
            return NumberT.from_ast(term)
        case "CCases":
            return MatchT.from_ast(term)
        case "CFix":
            return FixT.from_ast(term)
        case "CApp":
            return AppT.from_ast(term)
        case _:
            raise NotImplementedError(f"Unhandled Term Type: {term[0]}")


@dataclass
class StrTree:
    key: str
    children: list[StrTree]


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
        case _:
            raise ValueError(f"Unrecognized term class {attempted_name}")


def get_body_from_definition(ast: Any) -> Any:
    body = ast["v"]["expr"][1][3]
    assert isinstance(body, list)
    assert body[0] == "DefineBody"
    expr = body[3]
    return expr


def transform_ast(ast: Any) -> Term:
    pass
