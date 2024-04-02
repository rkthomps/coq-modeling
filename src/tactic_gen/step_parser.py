from __future__ import annotations
import os
from typing import Any, Optional, Union, Callable
from dataclasses import dataclass
import re
from enum import Enum
import logging

from util.util import LOGGER


class CoqParseError(Exception):
    pass


class SpecialToken(Enum):
    OPEN_COMMENT = 1
    CLOSE_COMMENT = 2
    OPEN_PAREN = 3
    CLOSE_PAREN = 4
    QUOTE = 5
    OPEN_SQ_BRACKET = 6
    CLOSE_SQ_BRACKET = 7
    OPEN_CURLY_BRACE = 8
    CLOSE_CURLY_BRANCE = 9
    OR_DISJUNCT = 10
    PERIOD = 11
    SEMICOLON = 12
    AS_TOK = 13
    ENTAIL_TOK = 14
    STAR = 15
    DASH = 16
    PLUS = 17
    COMMA = 18
    COLON = 19
    ASSIGN = 20
    RIGHT_ARROW = 21
    LEFT_ARROW = 22


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


Token = SpecialToken | StringTok | CommentTok | ExprTok | PatternTok | IdTok


def special2str(tok: SpecialToken) -> str:
    match tok:
        case SpecialToken.OPEN_COMMENT:
            return "(*"
        case SpecialToken.CLOSE_COMMENT:
            return "*)"
        case SpecialToken.OPEN_PAREN:
            return "("
        case SpecialToken.CLOSE_PAREN:
            return ")"
        case SpecialToken.QUOTE:
            return '"'
        case SpecialToken.OPEN_SQ_BRACKET:
            return "["
        case SpecialToken.CLOSE_SQ_BRACKET:
            return "]"
        case SpecialToken.OPEN_CURLY_BRACE:
            return "{"
        case SpecialToken.CLOSE_CURLY_BRANCE:
            return "}"
        case SpecialToken.OR_DISJUNCT:
            return "|"
        case SpecialToken.PERIOD:
            return "."
        case SpecialToken.SEMICOLON:
            return ";"
        case SpecialToken.AS_TOK:
            return "as"
        case SpecialToken.ENTAIL_TOK:
            return "|-"
        case SpecialToken.STAR:
            return "*"
        case SpecialToken.DASH:
            return "-"
        case SpecialToken.PLUS:
            return "+"
        case SpecialToken.COMMA:
            return ","
        case SpecialToken.COLON:
            return ":"
        case SpecialToken.ASSIGN:
            return ":="
        case SpecialToken.RIGHT_ARROW:
            return "->"
        case SpecialToken.LEFT_ARROW:
            return "<-"
        case _:
            raise ValueError("Unhandled special token.")


def norm(s: str) -> str:
    return tokens2str(normalize(lex(s)))


def try_norm(s: str) -> Optional[str]:
    try:
        return tokens2str(normalize(lex(s)))
    except CoqParseError:
        return None


def tokens2str(toks: list[Token]) -> str:
    str_toks: list[str] = []
    for token in toks:
        match token:
            case a if isinstance(a, SpecialToken):
                str_toks.append(special2str(a))
            case StringTok(contents=s):
                str_toks.append(f'"{s}"')
            case CommentTok(contents=s):
                str_toks.append(f"(*{s}*)")
            case ExprTok(expr=expr_list):
                str_toks.append(f"( {tokens2str(expr_list)} )")
            case PatternTok(args=args):
                str_toks.append(f"[ {tokens2str(args)} ]")
            case IdTok(name=n):
                str_toks.append(n)
            case _:
                raise ValueError("Unhandled token type.")
    return " ".join(str_toks)


ID_HOLE = "<ID>"
EXPR_HOLE = "<EXPR>"
STRING_HOLE = "<STR>"

keyword_set = {
    "intros",
    "apply",
    "reflexivity",
    "rewrite",
    "simpl",
    "destruct",
    "in",
    "auto",
    "as",
    "unfold",
    "induction",
    "intro",
    "split",
    "assumption",
    "with",
    "inversion",
    "assert",
    "exists",
    "exact",
    "subst",
    "lia",
    "case",
    "right",
    "elim",
    "trivial",
    "try",
    "left",
    "constructor",
    "clear",
    "by",
    "now",
    "tauto",
    "contradiction",
    "intuition",
    "generalize",
    "discriminate",
    "eauto",
    "pose",
    "repeat",
    "specialize",
    "=>",
    "eapply",
    "replace",
    "refine",
    "revert",
    "firstorder",
    "symmetry",
    "f_equal",
    "proof",
    "congruence",
    "using",
    "done",
    "Abort",
    "update",
    "arith",
    "move",
    "easy",
    "cut",
    "erewrite",
    "at",
    "datatypes",
    "injection",
    "dependent",
    "exfalso",
    "eqn",
    "t_update",
    "do",
    "contra",
    "change",
    "case_eq",
    "ring",
    "have",
    "absurd",
    "econstructor",
    "functional_extensionality",
    "transitivity",
    "contradict",
    "inclusion",
    "solve",
    "move",
    "match",
    "end",
    "eassumption",
    "Proof",
    "decidable",
    "decide",
    "equality",
    "compute",
    "inversion_clear",
    "forall_e",
    "empty",
    "exensionality",
    "admit",
    "compose",
    "Show",
    "subspec",
    "etransitivity",
    "and",
    "nia",
    "unshelve",
    "associativity",
    "refl",
    "eexists",
    "decompose",
    "progress",
    "abstract",
    "classic",
    "cofix",
    "equiv",
    "rename",
}


def get_id_strs(tokens: list[Token]) -> list[str]:
    match tokens:
        case [IdTok(name=a), *rest]:
            return [a] + get_id_strs(rest)
        case [PatternTok(args=args), *rest]:
            return get_id_strs(args) + get_id_strs(rest)
        case [a, *rest]:
            return get_id_strs(rest)
        case []:
            return []
        case _:
            raise ValueError("unhandled case")


def normalize(tokens: list[Token]) -> list[Token]:
    match tokens:
        case [IdTok(name=a), *rest] if a in keyword_set:
            return [IdTok(a)] + normalize(rest)
        case [CommentTok(), *rest]:
            return normalize(rest)
        case [ExprTok(), *rest]:
            return [IdTok(EXPR_HOLE)] + normalize(rest)
        case [PatternTok(args=args), *rest]:
            return [PatternTok(normalize(args))] + normalize(rest)
        case [IdTok(), *rest]:
            return [IdTok(ID_HOLE)] + normalize(rest)
        case [StringTok(), *rest]:
            return [IdTok(STRING_HOLE)] + normalize(rest)
        case [a, *rest] if isinstance(a, SpecialToken):
            return [a] + normalize(rest)
        case []:
            return []
        case _:
            raise ValueError(f"Unhandled token: {tokens}")


def lex(s: str) -> list[Token]:
    try:
        return __post_process(__lex([ch for ch in s]))
    except RecursionError:
        msg = f"Could not parse step: {s}"
        LOGGER.info(f"Could not parse step: {s}")
        raise CoqParseError(msg)


def __post_process(toks: list[Token]) -> list[Token]:
    match toks:
        case [IdTok(name=name1), SpecialToken.PERIOD, IdTok(name=name2), *rest]:
            return __post_process([IdTok(name1 + "." + name2)] + rest)
        case [ExprTok(expr=expr), *rest]:
            return [ExprTok(__post_process(expr))] + __post_process(rest)
        case [PatternTok(args=args), *rest]:
            return [PatternTok(__post_process(args))] + __post_process(rest)
        case [a, *rest]:
            return [a] + __post_process(rest)
        case []:
            return []
        case _:
            raise ValueError("Unhandled case.")


def __lex(chars: list[str]) -> list[Token]:
    match chars:
        case ["(", "*", *rest]:
            comment_tok, comment_rest = read_comment(rest)
            return [comment_tok] + __lex(comment_rest)
        case ['\\"', *rest]:
            id_tok, id_rest = read_id(chars)
            return [id_tok] + __lex(id_rest)
        case ['"', *rest]:
            str_tok, str_rest = read_str(rest)
            return [str_tok] + __lex(str_rest)
        case ["(", *rest]:
            expr_tok, expr_rest = read_expression(rest)
            return [expr_tok] + __lex(expr_rest)
        case ["[", *rest]:
            pattern_tok, pattern_rest = read_pattern(rest)
            return [pattern_tok] + __lex(pattern_rest)
        case ["<", "-", *rest]:
            return [SpecialToken.LEFT_ARROW] + __lex(rest)
        case ["-", ">", *rest]:
            return [SpecialToken.RIGHT_ARROW] + __lex(rest)
        case [":", "=", *rest]:
            return [SpecialToken.ASSIGN] + __lex(rest)
        case ["|", "-", *rest]:
            return [SpecialToken.ENTAIL_TOK] + __lex(rest)
        case ["+", *rest]:
            return [SpecialToken.PLUS] + __lex(rest)
        case ["-", *rest]:
            return [SpecialToken.DASH] + __lex(rest)
        case ["*", *rest]:
            return [SpecialToken.STAR] + __lex(rest)
        case [".", *rest]:
            return [SpecialToken.PERIOD] + __lex(rest)
        case [";", *rest]:
            return [SpecialToken.SEMICOLON] + __lex(rest)
        case [":", *rest]:
            return [SpecialToken.COLON] + __lex(rest)
        case ["{", *rest]:
            return [SpecialToken.OPEN_CURLY_BRACE] + __lex(rest)
        case ["}", *rest]:
            return [SpecialToken.CLOSE_CURLY_BRANCE] + __lex(rest)
        case ["|", *rest]:
            return [SpecialToken.OR_DISJUNCT] + __lex(rest)
        case [",", *rest]:
            return [SpecialToken.COMMA] + __lex(rest)
        case [a, *rest] if re.match(r"\s", a):
            return __lex(rest)
        case [a, *rest]:
            id_tok, id_rest = read_id(chars)
            return [id_tok] + __lex(id_rest)
        case []:
            return []
        case _:
            raise ValueError("Unknown parse error.")


def read_id(chars: list[str]) -> tuple[IdTok, list[str]]:
    match chars:
        case [a, *rest] if re.match(r"\s", a):
            return IdTok(""), rest
        case ["(", "*", *rest]:
            return IdTok(""), chars
        case [a, *rest] if a in [")", "]", ".", ";", "|", ",", "(", "[", ":"]:
            return IdTok(""), chars
        case [a, *rest]:
            remaining_id_tok, id_rest = read_id(rest)
            return IdTok(a + remaining_id_tok.name), id_rest
        case _:
            raise ValueError("Error parsing Id.")


def read_pattern(chars: list[str]) -> tuple[PatternTok, list[str]]:
    match chars:
        case ["]", *rest]:
            return PatternTok([]), rest
        case ["(", "*", *rest]:
            comment_tok, comment_rest = read_comment(rest)
            remaining_pattern_tok, remaining_toks = read_pattern(comment_rest)
            return (
                PatternTok([comment_tok] + remaining_pattern_tok.args),
                remaining_toks,
            )
        case ['\\"', *rest]:
            id_tok, id_rest = read_id(chars)
            remaining_pattern_tok, remaining_toks = read_pattern(id_rest)
            return PatternTok([id_tok] + remaining_pattern_tok.args), remaining_toks
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
        case [";", *rest]:
            remaining_pattern_tok, remaining_toks = read_pattern(rest)
            return (
                PatternTok([SpecialToken.SEMICOLON] + remaining_pattern_tok.args),
                remaining_toks,
            )
        case [":", "=", *rest]:
            remaining_pattern_tok, remaining_toks = read_pattern(rest)
            return (
                PatternTok([SpecialToken.ASSIGN] + remaining_pattern_tok.args),
                remaining_toks,
            )
        case ["<", "-", *rest]:
            remaining_pattern_tok, remaining_toks = read_pattern(rest)
            return (
                PatternTok([SpecialToken.LEFT_ARROW] + remaining_pattern_tok.args),
                remaining_toks,
            )
        case ["-", ">", *rest]:
            remaining_pattern_tok, remaining_toks = read_pattern(rest)
            return (
                PatternTok([SpecialToken.RIGHT_ARROW] + remaining_pattern_tok.args),
                remaining_toks,
            )
        case [":", *rest]:
            remaining_pattern_tok, remaining_toks = read_pattern(rest)
            return (
                PatternTok([SpecialToken.COLON] + remaining_pattern_tok.args),
                remaining_toks,
            )
        case [".", *rest]:
            remaining_pattern_tok, remaining_toks = read_pattern(rest)
            return (
                PatternTok([SpecialToken.PERIOD] + remaining_pattern_tok.args),
                remaining_toks,
            )
        case [a, *rest] if re.match(r"\s", a):
            return read_pattern(rest)
        case [a, *rest]:
            id_tok, id_rest = read_id(chars)
            remaining_pattern_tok, remaining_toks = read_pattern(id_rest)
            return PatternTok([id_tok] + remaining_pattern_tok.args), remaining_toks
        case _:
            raise ValueError("Unterminated pattern.")


def read_expression(chars: list[str]) -> tuple[ExprTok, list[str]]:
    match chars:
        case ["(", "*", *rest]:
            comment_tok, comment_rest = read_comment(rest)
            remaining_expr_tok, remaining_toks = read_expression(comment_rest)
            return ExprTok([comment_tok] + remaining_expr_tok.expr), remaining_toks
        case ['\\"', *rest]:
            id_tok, id_rest = read_id(chars)
            remaining_expr_tok, remaining_toks = read_expression(id_rest)
            return ExprTok([id_tok] + remaining_expr_tok.expr), remaining_toks
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
        case [".", *rest]:
            remaining_expr_tok, remaining_toks = read_expression(rest)
            return (
                ExprTok([SpecialToken.PERIOD] + remaining_expr_tok.expr),
                remaining_toks,
            )
        case [",", *rest]:
            remaining_expr_tok, remaining_toks = read_expression(rest)
            return (
                ExprTok([SpecialToken.COMMA] + remaining_expr_tok.expr),
                remaining_toks,
            )
        case ["[", *rest]:
            remaining_expr_tok, remaining_toks = read_expression(rest)
            return (
                ExprTok([SpecialToken.OPEN_SQ_BRACKET] + remaining_expr_tok.expr),
                remaining_toks,
            )
        case ["]", *rest]:
            remaining_expr_tok, remaining_toks = read_expression(rest)
            return (
                ExprTok([SpecialToken.CLOSE_SQ_BRACKET] + remaining_expr_tok.expr),
                remaining_toks,
            )
        case [";", *rest]:
            remaining_expr_tok, remaining_toks = read_expression(rest)
            return (
                ExprTok([SpecialToken.SEMICOLON] + remaining_expr_tok.expr),
                remaining_toks,
            )
        case [":", "=", *rest]:
            remaining_expr_tok, remaining_toks = read_expression(rest)
            return (
                ExprTok([SpecialToken.ASSIGN] + remaining_expr_tok.expr),
                remaining_toks,
            )
        case [":", *rest]:
            remaining_expr_tok, remaining_toks = read_expression(rest)
            return (
                ExprTok([SpecialToken.COLON] + remaining_expr_tok.expr),
                remaining_toks,
            )
        case ["|", *rest]:
            remaining_expr_tok, remaining_toks = read_expression(rest)
            return (
                ExprTok([SpecialToken.OR_DISJUNCT] + remaining_expr_tok.expr),
                remaining_toks,
            )
        case [a, *rest] if re.match(r"\s", a):
            return read_expression(rest)
        case [a, *rest]:
            id_tok, id_rest = read_id(chars)
            remaining_expr_tok, remaining_toks = read_expression(id_rest)
            return ExprTok([id_tok] + remaining_expr_tok.expr), remaining_toks
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
