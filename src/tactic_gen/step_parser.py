from __future__ import annotations
from typing import Any, Optional, Union, Callable
from dataclasses import dataclass
import re
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


@dataclass
class NormalChar:
    char: str


@dataclass
class StringTok:
    contents: str


@dataclass
class CommentTok:
    contents: str


@dataclass
class ExprTok:
    expr: list[Token]


@dataclass
class IdTok:
    name: str


@dataclass
class PatternTok:
    args: list[Token]


Token = (
    SpecialToken | NormalChar | StringTok | CommentTok | ExprTok | PatternTok | IdTok
)


def lex(s: str) -> list[Token]:
    return __lex([ch for ch in s])


def __lex(chars: list[str]) -> list[Token]:
    match chars:
        case ["(", "*", *rest]:
            comment_tok, comment_rest = read_comment(rest)
            return [comment_tok] + __lex(comment_rest)
        case ['\\"', *rest]:
            return [NormalChar('\\"')] + __lex(rest)
        case ['"', *rest]:
            str_tok, str_rest = read_str(rest)
            return [str_tok] + __lex(str_rest)
        case ["(", *rest]:
            expr_tok, expr_rest = read_expression(rest)
            return [expr_tok] + __lex(expr_rest)
        case ["[", *rest]:
            pattern_tok, pattern_rest = read_pattern(rest)
            return [pattern_tok] + __lex(pattern_rest)
        case [".", *rest]:
            return [SpecialToken.PERIOD] + __lex(rest)
        case [";", *rest]:
            return [SpecialToken.SEMICOLON] + __lex(rest)
        case [a, *rest] if re.match(r"\s", a):
            return __lex(rest)
        case [a, *rest]:
            id_tok, id_rest = read_id([a] + rest)
            return [id_tok] + __lex(id_rest)
        case []:
            return []
        case _:
            raise ValueError("Unknown parse error.")


def read_id(chars: list[str]) -> tuple[IdTok, list[str]]:
    match chars:
        case [a, *rest] if re.match(r"\s", a):
            return IdTok(""), rest
        case [".", *rest]:
            return IdTok(""), ["."] + rest
        case [a, *rest]:
            remaining_id_tok, id_rest = read_id(rest)
            return IdTok(a + remaining_id_tok.name), id_rest
        case _:
            raise ValueError("Error parsing Id.")


def read_pattern(chars: list[str]) -> tuple[PatternTok, list[str]]:
    match chars:
        case ["(", "*", *rest]:
            comment_tok, comment_rest = read_comment(rest)
            remaining_pattern_tok, remaining_toks = read_pattern(comment_rest)
            return (
                PatternTok([comment_tok] + remaining_pattern_tok.args),
                remaining_toks,
            )
        case ['\\"', *rest]:
            remaining_pattern_tok, remaining_toks = read_pattern(rest)
            return (
                PatternTok([NormalChar('\\"')] + remaining_pattern_tok.args),
                remaining_toks,
            )
        case ['"', *rest]:
            str_tok, str_rest = read_str(rest)
            remaining_pattern_tok, remaining_toks = read_pattern(str_rest)
            return PatternTok([str_tok] + remaining_pattern_tok.args), remaining_toks
        case ["(", *rest]:
            expr_tok, expr_rest = read_expression(rest)
            remaining_pattern_tok, remaining_toks = read_pattern(expr_rest)
            return PatternTok([expr_tok] + remaining_pattern_tok.args), remaining_toks
        case ["[", *rest]:
            pattern_tok, pattern_rest = read_pattern(rest)
            remaining_pattern_tok, remaining_toks = read_pattern(pattern_rest)
            return (
                PatternTok([pattern_tok] + remaining_pattern_tok.args),
                remaining_toks,
            )
        case ["|", *rest]:
            remaining_pattern_tok, remaining_toks = read_pattern(rest)
            return (
                PatternTok([SpecialToken.OR_DISJUNCT] + remaining_pattern_tok.args),
                remaining_toks,
            )
        case _:
            raise ValueError("Unterminated pattern.")


def read_expression(chars: list[str]) -> tuple[ExprTok, list[str]]:
    match chars:
        case ["(", "*", *rest]:
            comment_tok, comment_rest = read_comment(rest)
            remaining_expr_tok, remaining_toks = read_expression(comment_rest)
            return ExprTok([comment_tok] + remaining_expr_tok.expr), remaining_toks
        case ['\\"', *rest]:
            remaining_expr_tok, remaining_toks = read_expression(rest)
            return (
                ExprTok([NormalChar('\\"')] + remaining_expr_tok.expr),
                remaining_toks,
            )
        case ['"', *rest]:
            str_tok, new_rest = read_str(rest)
            remaining_expr_tok, remaining_toks = read_expression(new_rest)
            return ExprTok([str_tok] + remaining_expr_tok.expr), remaining_toks
        case ["(", *rest]:
            expr_tok, new_rest = read_expression(rest)
            remaining_expr_tok, remaining_toks = read_expression(new_rest)
            return ExprTok([expr_tok] + remaining_expr_tok.expr), remaining_toks
        case [")", *rest]:
            return ExprTok([]), rest
        case [a, *rest]:
            remaining_expr_tok, remaining_toks = read_expression(rest)
            return ExprTok([NormalChar(a)] + remaining_expr_tok.expr), remaining_toks
        case _:
            raise ValueError("Unclosed Expression.")


def read_comment(chars: list[str]) -> tuple[CommentTok, list[str]]:
    match chars:
        case ["*", ")", *rest]:
            return CommentTok(""), rest
        case [a, *rest]:
            remaining_comment, remaining_chars = read_comment(rest)
            return CommentTok(a + remaining_comment.contents), remaining_chars
        case _:
            raise ValueError("Unfinished comment.")


def read_str(chars: list[str]) -> tuple[StringTok, list[str]]:
    match chars:
        case ['"', *rest]:
            return StringTok(""), rest
        case [a, *rest]:
            remaining_string, remaining_chars = read_str(rest)
            return StringTok(a + remaining_string.contents), remaining_chars
        case _:
            raise ValueError("Unfinished string.")
