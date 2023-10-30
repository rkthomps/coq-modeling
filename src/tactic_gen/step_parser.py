from __future__ import annotations
from typing import Any, Optional, Union
from enum import Enum


class SpecialToken(Enum):
    OPEN_COMMENT = 1
    CLOSE_COMMENT = 2
    OPEN_PAREN = 3
    CLOSE_PAREN = 4
    QUOTE = 5
    OPEN_BRACKET = 6
    CLOSE_BRACKET = 7
    OR_DISJUNCT = 8
    PERIOD = 9
    SEMICOLON = 10

class NormalChar:
    def __init__(self, char: str) -> None:
        assert type(char) == str
        assert len(char) == 1
        self.char = char

class StringTok:
    def __init__(self, contents: str) -> None:
        assert type(contents) == str
        self.contents = contents

class CommentTok:
    def __init__(self, contents: str) -> None:
        assert type(contents) == str
        self.contents = contents

class ExprTok:
    def __init__(self, expr: list[Token]) -> None:
        self.expr = expr


Token = SpecialToken | NormalChar | StringTok | CommentTok
def lex(chars: list[str]) -> list[Token]:
    match chars:
        case ["(", "*", *rest]:
            comment_tok, rest = read_comment(rest)
            return [SpecialToken.OPEN_COMMENT, comment_tok, SpecialToken.CLOSE_COMMENT] + lex(rest)
        case ["\\\"", *rest]:
            return [NormalChar("\\\"")] + lex(rest)
        case ["\"", *rest]:
            return [SpecialToken.QUOTE, read_str, SpecialToken.QUOTE] + lex(rest)
        case [".", *rest]:
            return [SpecialToken.PERIOD] + lex(rest)
        case [";", *rest]:
            return [SpecialToken.SEMICOLON] + lex(rest)
        case ["(", *rest]:
            return [SpecialToken.OPEN_PAREN] + lex(rest)
        case [")", *rest]:
            return [SpecialToken.CLOSE_PAREN] + lex(rest)
        case ["[", *rest]:
            return [SpecialToken.OPEN_BRACKET] + lex(rest)
        case ["]", *rest]:
            return [SpecialToken.CLOSE_BRACKET] + lex(rest)
        case [a, *rest]:
            return [NormalChar(a)] + lex(rest)
        case []:
            return []

def read_expression(chars: list[str]) -> tuple[ExprTok, list[str]]:
    match chars:
        case ["(", "*", *rest]:
            comment_tok, rest = read_comment(rest)
            comment_toks = [SpecialToken.OPEN_COMMENT, comment_tok, SpecialToken.CLOSE_COMMENT]
            remaining_expr_tok, remaining_toks = read_expression(rest)
            return ExprTok(comment_toks + remaining_expr_tok.expr), remaining_toks
        case ["\\\"", *rest]:
            remaining_expr_tok, remaining_toks = read_expression(rest)
            return ExprTok(["\\\""] + remaining_expr_tok.expr), remaining_toks
        case ["\"", *rest]:
            str_tok, rest = read_str(rest)
            str_toks = [SpecialToken.QUOTE, str_tok, SpecialToken.QUOTE]
            remaining_expr_tok, remaining_toks = read_expression(rest)
            return ExprTok(str_toks + remaining_expr_tok.expr), remaining_toks
        case ["(", *rest]:
            expr_tok, rest = read_expression(rest)
            pass


def read_comment(chars: list[str]) -> tuple[CommentTok, list[str]]:
    match chars:
        case ["*", ")", *rest]:
            return CommentTok(""), rest
        case [a, *rest]:
            remaining_comment, remaining_chars = read_comment(rest)
            return CommentTok(a + remaining_comment.contents), remaining_chars
        case []:
            raise ValueError("Unfinished comment.")

def read_str(chars: list[str]) -> tuple[StringTok, list[str]]:
    match chars:
        case ["\"", *rest]:
            return StringTok(""), rest
        case [a, *rest]:
            remaining_string, remaining_chars = read_str(rest)
            return StringTok(a + remaining_string.contents), remaining_chars
        case []:
            raise ValueError("Unfinished string.")

def read_expr(chars: list[str]) -> tuple[list[NormalChar], list[str]]:
    match chars:
        case [")", *rest]:
            return [], rest
        case [a, *rest]:
            re


class ProofSentence:
    def __init__(self, command_list: list[Command]) -> None:
        pass
    
    @classmethod
    def from_string(cls, s: str) -> ProofSentence:
        


class Command:
    def __init__(
        self,
        command: str,
        args: list[Expression],
        pattern: Optional[Pattern],
        annotation: Optional[str],
    ) -> None:
        pass


class PatternType(Enum):
    DISJUNCTIVE = 1
    CONJUNCTIVE = 2


class Pattern:
    def __init__(self, pattern_type: PatternType, pattern_contents: list[PatternArg]):
        pass

PatternArg = Union[str, Pattern]


class Expression:
    def __init__(self, contents: Any) -> None:
        pass
