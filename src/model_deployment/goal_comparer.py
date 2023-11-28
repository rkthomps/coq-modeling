from __future__ import annotations
from coqpyt.coq.structs import Step, RangedSpan
from coqpyt.coq.lsp.structs import Goal
from typing import Any, Optional
import pdb

from typeguard import typechecked

from model_deployment.search_tree import ProofSearchTree


def extract_body_from_step(step: Step) -> Any:
    def_ast = remove_loc(step.ast.span)
    def_expr = def_ast["v"]["expr"][1]
    try:
        assert def_expr[0] == "VernacDefinition"
    except AssertionError:
        pdb.set_trace()
    return def_expr[3]


@typechecked
class ParsedHyp:
    def __init__(self, ids: list[str], ast: Any) -> None:
        self.ids = ids
        self.ast = ast


@typechecked
class ParsedObligation:
    def __init__(self, hyps: list[ParsedHyp], goal_ast: Any) -> None:
        self.hyps = hyps
        self.goal_ast = goal_ast

    def get_all_vars(self) -> list[str]:
        all_vars: list[str] = []
        for hyp in self.hyps:
            for var in hyp.ids:
                all_vars.append(var)
        return all_vars

    def get_hyp_from_var(self, var: str) -> ParsedHyp:
        for hyp in self.hyps:
            if var in hyp.ids:
                return hyp
        raise ValueError(f"Hyp {var} doesn't exist.")

    def __check_substitution_validity(
        self,
        other: ParsedObligation,
        one_to_two_mapping: dict[str, Optional[str]],
        two_avail_vars: set[str],
    ) -> bool:
        for var in self.get_all_vars():
            corresponding_var = one_to_two_mapping[var]
            if corresponding_var is None:
                continue
            other_hyp = other.get_hyp_from_var(corresponding_var)
            self_hyp = self.get_hyp_from_var(var)
            fresh_var_mapping: dict[str, str] = {}
            hyps_same = compare_expressions_under_substitution(
                self_hyp.ast,
                other_hyp.ast,
                one_to_two_mapping,
                two_avail_vars,
                fresh_var_mapping,
            )
            if not hyps_same:
                return False
        return True

    def __append_if_absent(
        self,
        mapping_candidates: list[dict[str, Optional[str]]],
        new_candidate: dict[str, Optional[str]],
    ) -> None:
        if any([m == new_candidate for m in mapping_candidates]):
            return
        mapping_candidates.append(new_candidate)

    def __check_hyps_covered(
        self,
        other: ParsedObligation,
        one_to_two_mapping: dict[str, Optional[str]],
        two_avail_vars: set[str],
    ) -> bool:
        """
        Must keep track of multiple possible matches. Consider the hyps:
        a = b       b = c
        b < a       b < a
        b = c       a = b
        ---         ---
        False       False

        These are clearly equiv. but if you matched greedily, you would end up in a pickle
        """
        mapping_candidates: list[dict[str, Optional[str]]] = [one_to_two_mapping.copy()]
        for self_hyp in self.hyps:
            next_mapping_candidates: list[dict[str, Optional[str]]] = []
            for other_hyp in other.hyps:
                for mapping in mapping_candidates:
                    fresh_var_mapping: dict[str, str] = {}
                    copied_mapping = mapping.copy()
                    if compare_expressions_under_substitution(
                        self_hyp.ast,
                        other_hyp.ast,
                        copied_mapping,
                        two_avail_vars,
                        fresh_var_mapping,
                    ):
                        self.__append_if_absent(next_mapping_candidates, copied_mapping)
            if len(next_mapping_candidates) == 0:
                return False
            mapping_candidates = next_mapping_candidates
        return True

    def as_hard_as(self, other: ParsedObligation) -> bool:
        self_vars = self.get_all_vars()
        one_to_two_mapping: dict[str, str | None] = dict((k, None) for k in self_vars)
        two_avail_vars = set(other.get_all_vars())
        fresh_var_mapping: dict[str, str] = {}
        same_goal_under_sub = compare_expressions_under_substitution(
            self.goal_ast,
            other.goal_ast,
            one_to_two_mapping,
            two_avail_vars,
            fresh_var_mapping,
        )
        if not same_goal_under_sub:
            return False

        substitution_valid = self.__check_substitution_validity(
            other, one_to_two_mapping, two_avail_vars
        )
        if not substitution_valid:
            return False

        hyps_covered = self.__check_hyps_covered(
            other, one_to_two_mapping, two_avail_vars
        )
        return hyps_covered


@typechecked
class ParsedObligations:
    def __init__(self, obligations: list[ParsedObligation]) -> None:
        self.obligations = obligations

    def as_hard_as(self, other: ParsedObligations) -> bool:
        for other_ob in other.obligations:
            covered = False
            for self_ob in self.obligations:
                if self_ob.as_hard_as(other_ob):
                    covered = True
                    break
            if not covered:
                return False
        return True

    def redundant_to(
        self,
        other_obligations: list[ParsedObligations],
        other_nodes: list[ProofSearchTree],
    ) -> Optional[ProofSearchTree]:
        for i, other in enumerate(other_obligations):
            if self.as_hard_as(other):
                return other_nodes[i]
        return None


class CoqName:
    def __init__(self, id: str) -> None:
        assert type(id) == str
        self.id = id

    @classmethod
    def from_json(cls, json_data: Any) -> CoqName:
        """Example: ["Name", ["Id", "l"]]"""
        match json_data:
            case ["Name", ["Id", name]]:
                return cls(name)
            case _:
                raise ValueError(
                    (
                        f"Shape of CoqName incorrect. "
                        'Expected ["Name", ["Id", _]]. Got {json_data}'
                    )
                )


@typechecked
class CoqQualId:
    def __init__(self, dirpath: list[list[str]], id: str) -> None:
        self.dirpath = dirpath
        self.id = id

    def __hash__(self) -> int:
        all_tokens: list[str] = []
        for o_dirpath in self.dirpath:
            for i_str in o_dirpath:
                all_tokens.append(i_str)
        return hash((self.id, "|".join(all_tokens)))

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, CoqQualId):
            return False
        return hash(self) == hash(other)

    @classmethod
    def from_json(cls, json_data: Any) -> CoqQualId:
        """Ex: ['Ser_Qualid', ['DirPath', []], ['Id', 'Some']]"""
        match json_data:
            case ["Ser_Qualid", ["DirPath", d], ["Id", name]]:
                return cls(d, name)
            case _:
                raise ValueError(
                    (
                        f"Expected Qualid to have shape "
                        f'["Ser_Qualid", ["DirPath", <dirpath>], ["Id", <id>]] '
                        f"got {json_data}"
                    )
                )


def __is_local_assm(ast: Any) -> bool:
    match ast:
        case ["CLocalAssum", *_]:
            return True
        case [h, *_]:
            return __is_local_assm(h)
        case _:
            return False


def __compare_dicts_under_substitution(
    goal1_ast: dict[Any, Any],
    goal2_ast: Any,
    one_to_two_mapping: dict[str, Optional[str]],
    avail_names_two: set[str],
    fresh_var_mapping: dict[str, str],
) -> bool:
    if not isinstance(goal2_ast, dict):
        return False
    if len(goal1_ast) != len(goal2_ast):
        return False
    for k, v in goal1_ast.items():
        if k == "loc":
            continue
        if k not in goal2_ast:
            return False
        values_equal = compare_expressions_under_substitution(
            v, goal2_ast[k], one_to_two_mapping, avail_names_two, fresh_var_mapping
        )
        if not values_equal:
            return False
    return True


def __compare_qualid_under_substitution(
    exp1_ast: list[Any],
    exp2_ast: list[Any],
    one_to_two_mapping: dict[str, Optional[str]],
    avail_names_two: set[str],
    fresh_var_mapping: dict[str, str],
) -> bool:
    assert exp1_ast[0] == "Ser_Qualid"
    qual1 = CoqQualId.from_json(exp1_ast)
    try:
        qual2 = CoqQualId.from_json(exp2_ast)
    except AssertionError:
        return False

    if qual1.id in fresh_var_mapping:
        return fresh_var_mapping[qual1.id] == qual2.id

    if qual1.id in one_to_two_mapping:
        if one_to_two_mapping[qual1.id] is None:
            if qual2.id not in avail_names_two:
                return False
            one_to_two_mapping[qual1.id] = qual2.id
            return True
        else:
            return one_to_two_mapping[qual1.id] == qual2.id

    return qual1 == qual2


def __compare_names_under_substitution(
    exp1_ast: list[Any],
    exp2_ast: list[Any],
    one_to_two_mapping: dict[str, Optional[str]],
    avail_names_two: set[str],
    fresh_var_mapping: dict[str, str],
) -> bool:
    assert exp1_ast[0] == "Name"
    name1 = CoqName.from_json(exp1_ast)
    try:
        name2 = CoqName.from_json(exp2_ast)
    except AssertionError:
        return False
    assert name1.id not in one_to_two_mapping
    assert name2.id not in avail_names_two
    # Unfortunately I can't make a copy and pass to subtree since this is leaf
    fresh_var_mapping[name1.id] = name2.id
    return True


def __compare_lists_under_substitution(
    exp1_ast: list[Any],
    exp2_ast: Any,
    one_to_two_mapping: dict[str, Optional[str]],
    avail_names_two: set[str],
    fresh_var_mapping: dict[str, str],
) -> bool:
    assert type(exp1_ast) == list
    if not isinstance(exp2_ast, list):
        return False
    if len(exp1_ast) == 0:
        return len(exp2_ast) == 0
    if exp1_ast[0] == "Ser_Qualid":
        return __compare_qualid_under_substitution(
            exp1_ast, exp2_ast, one_to_two_mapping, avail_names_two, fresh_var_mapping
        )
    if exp1_ast[0] == "Name":
        return __compare_names_under_substitution(
            exp1_ast, exp2_ast, one_to_two_mapping, avail_names_two, fresh_var_mapping
        )
    if len(exp1_ast) != len(exp2_ast):
        return False

    # Since the asts annoyingly can list uses before defs,
    # we have to explicitly put defs first
    ast1_to_compare_first: list[Any] = []
    ast1_to_compare_second: list[Any] = []
    ast2_to_compare_first: list[Any] = []
    ast2_to_compare_second: list[Any] = []
    for exp1_el, exp2_el in zip(exp1_ast, exp2_ast):
        if __is_local_assm(exp1_el):
            ast1_to_compare_first.append(exp1_el)
            ast2_to_compare_first.append(exp2_el)
        else:
            ast1_to_compare_second.append(exp1_el)
            ast2_to_compare_second.append(exp2_el)

    ast1_to_compare = ast1_to_compare_first + ast1_to_compare_second
    ast2_to_compare = ast2_to_compare_first + ast2_to_compare_second
    assert len(ast1_to_compare) == len(ast2_to_compare)
    assert len(ast2_to_compare) == len(exp1_ast)
    # Look for Names first as they sometimes come later in the AST
    for exp1_el, exp2_el in zip(ast1_to_compare, ast2_to_compare):
        expr_eq = compare_expressions_under_substitution(
            exp1_el, exp2_el, one_to_two_mapping, avail_names_two, fresh_var_mapping
        )
        if not expr_eq:
            return False
    return True


def compare_expressions_under_substitution(
    exp1_ast: Any,
    exp2_ast: Any,
    one_to_two_mapping: dict[str, Optional[str]],
    avail_names_two: set[str],
    fresh_var_mapping: dict[str, str],
) -> bool:
    if type(exp1_ast) == dict:
        return __compare_dicts_under_substitution(
            exp1_ast, exp2_ast, one_to_two_mapping, avail_names_two, fresh_var_mapping
        )

    if type(exp1_ast) == list:
        return __compare_lists_under_substitution(
            exp1_ast, exp2_ast, one_to_two_mapping, avail_names_two, fresh_var_mapping
        )

    if exp1_ast is None and exp2_ast is None:
        return True
    assert (
        exp1_ast is None
        or type(exp1_ast) == str
        or type(exp1_ast) == int
        or type(exp1_ast) == bool
        or type(exp1_ast) == float
    )
    if type(exp1_ast) != type(exp2_ast):
        return False
    return exp1_ast == exp2_ast


def remove_loc(d: Any) -> Any:
    if type(d) == dict:
        dict_result = {}
        for k, v in d.items():
            if k == "loc":
                continue
            dict_result[k] = remove_loc(v)
        return dict_result

    if type(d) == list:
        list_result = []
        for e in d:
            list_result.append(remove_loc(e))
        return list_result
    return d


def extract_last_definition_body(ast: list[RangedSpan]) -> Any:
    assert ast[-1].span is None
    last_period = ast[-2].span
    def_expr = last_period["v"]["expr"]
    assert def_expr[0] == "VernacDefinition"
    return def_expr[3]
