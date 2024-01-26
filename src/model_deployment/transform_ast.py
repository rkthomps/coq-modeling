from __future__ import annotations
from typing import Any
from typeguard import typechecked


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
    def from_ast(cls, ast: Any) -> NumberT:
        assert isinstance(ast, list)
        assert ast[0] == "CPrim"
        assert len(ast) == 2
        assert ast[1][0] == ["SPlus"]
        return cls(ast[1][1]["int"], ast[1][1]["frac"], ast[1][1]["exp"])


@typechecked
class QualIdT:
    def __init__(self, quals: list[str], id: str) -> None:
        self.quals = quals
        self.id = id

    def to_json(self) -> Any:
        return {
            "quals": self.quals,
            "id": self.id,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> QualIdT:
        return cls(json_data["quals"], json_data["id"])

    @classmethod
    def from_ast(cls, ast: Any) -> QualIdT:
        assert isinstance(ast, list)
        assert len(ast) == 3
        assert ast[0] == "CRef"
        assert isinstance(ast[1], dict)
        qualid_list = ast[1]["v"]
        assert len(qualid_list) == 3
        assert qualid_list[1][0] == "DirPath"
        dir_list = qualid_list[1][1]
        assert qualid_list[2][0] == "Id"
        id = qualid_list[2][1]
        return cls(dir_list, id)


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


Term = FunT | ProdT | QualIdT | NumberT


def term_from_ast(ast: Any) -> Term:
    assert isinstance(ast, dict)
    term = ast["v"]
    match term[0]:
        case "CLambdaN":
            return FunT.from_ast(term)
        case "CRef":
            return QualIdT.from_ast(term)
        case "CProdN":
            return ProdT.from_ast(term)
        case "CPrim":
            return NumberT.from_ast(term)
        case _:
            raise NotImplementedError(f"Unhandled Term Type: {term[0]}")


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
