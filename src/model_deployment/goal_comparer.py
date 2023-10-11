
from __future__ import annotations
from coqlspclient.coq_lsp_structs import Goal, RangedSpan
from typing import Any, Optional
import pdb


class ParsedHyp:
    def __init__(self, ids: list[str], ast: Any) -> None:
        assert all([type(i) == str for i in ids])
        self.ids = ids
        self.ast = ast


class ParsedObligation:
    def __init__(self, hyps: list[ParsedHyp], goal_ast: Any) -> None:
        assert all([type(h) == ParsedHyp for h in hyps])
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

    def as_hard_as(self, other: ParsedObligation) -> bool:
        self_vars = self.get_all_vars()
        one_to_two_mapping = dict((k, None) for k in self_vars)  
        two_avail_vars = set(other.get_all_vars())
        same_goal_under_sub = compare_expressions_under_substitution(
            self.goal_ast, other.goal_ast, one_to_two_mapping, two_avail_vars)
        if not same_goal_under_sub:
            return False
        for var in self_vars:
            if one_to_two_mapping[var] is None:
                continue
            self_hyp = self.get_hyp_from_var(var)
            other_hyp = other.get_hyp_from_var(one_to_two_mapping[var])
            hyps_same = compare_expressions_under_substitution(
                self_hyp.ast, other_hyp.ast, one_to_two_mapping, two_avail_vars)
            if not hyps_same:
                return False
        
        for self_hyp in self.hyps:
            covered = False
            for other_hyp in other.hyps:
                if compare_expressions_under_substitution(
                    self_hyp, other_hyp, one_to_two_mapping, two_avail_vars):
                    covered = True
                    break
            if not covered:
                return False
        return True


class ParsedObligations:
    def __init__(self, obligations: list[ParsedObligation]) -> None:
        assert all([type(o) == ParsedObligation for o in obligations])
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

    def makes_progress(self, others: list[ParsedObligations]) -> bool:
        for other in others:
            if self.as_hard_as(other):
                return False
        return True


class Obligation:
    def __init__(self, goal: Goal) -> None:
        self.goal = goal
    
    def as_hard_as(self, other: Obligation) -> bool:
        """This obligation is as hard as other if it
           has the same number or fewer hyps."""
        if self.goal.ty != other.goal.ty:
            return False
        this_hyps_covered: list[bool] = []
        for this_hyp in self.goal.hyps:
            this_hyp_covered = False 
            for other_hyp in other.goal.hyps: 
                if (sorted(this_hyp.names) == sorted(other_hyp.names) and
                    this_hyp.ty == other_hyp.ty):
                    this_hyp_covered = True
            this_hyps_covered.append(this_hyp_covered)
        return all(this_hyps_covered)


class NodeGoal:
    def __init__(self, goals: list[Goal]) -> None:
        self.obligations = [Obligation(g) for g in goals]

    def as_hard_as(self, other: NodeGoal) -> bool:
        """This list of obligations is as hard as other if it
           has the same or more goals"""
        other_obligations_covered: list[bool] = []
        for other_obligation in other.obligations:
            other_obligation_covered = False
            for this_obligation in self.obligations:
                if this_obligation.as_hard_as(other_obligation):
                    other_obligation_covered = True
            other_obligations_covered.append(other_obligation_covered)
        return all(other_obligations_covered)

    def makes_progress(self, others: list[NodeGoal]) -> bool:
        """A set of obligations 'makes progress' if it is strictly easier than
           any previously seen set of obligations"""
        for other in others:
            if self.as_hard_as(other):
                return False
        return True


class CoqName:
    def __init__(self, id: str) -> None:
        assert type(id) == str
        self.id = id
    
    @classmethod
    def from_json(cls, json_data: Any) -> CoqName:
        """Example: ["Name", ["Id", "l"]]"""
        assert type(json_data) == list 
        assert len(json_data) == 2
        assert json_data[0] == "Name"
        assert json_data[1][0] == "Id"
        return cls(json_data[1][1])
        

class CoqQualId:
    def __init__(self, dirpath: list[str], id: str) -> None:
        assert all([type(s) == str for s in dirpath])
        assert type(id) == str
        self.dirpath = dirpath
        self.id = id

    def __hash__(self) -> int:
        return hash((self.id, "|".join(self.dirpath)))

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, CoqQualId):
            return False
        return hash(self) == hash(other)
    

    @classmethod
    def from_json(cls, json_data: Any) -> CoqQualId:
        """Ex: ['Ser_Qualid', ['DirPath', []], ['Id', 'Some']]"""
        assert type(json_data) == list
        assert len(json_data) == 3
        assert json_data[0] == "Ser_Qualid"
        assert json_data[1][0] == "DirPath"
        assert json_data[2][0] == "Id"
        return cls(json_data[1][1], json_data[2][1])


def __is_local_assm(ast: Any) -> bool:
    if type(ast) != list:
        return False
    if len(ast) == 0:
        return False
    if ast[0] == "CLocalAssum":
        return True
    return __is_local_assm(ast[0])


def __compare_dicts_under_substitution(
        goal1_ast: dict[Any, Any],
        goal2_ast: Any,
        one_to_two_mapping: dict[str, Optional[str]],
        avail_names_two: set[str]) -> bool:
    assert type(goal1_ast) == dict
    if type(goal2_ast) != dict:
        return False
    if len(goal1_ast) != len(goal2_ast):
        return False
    for k, v in goal1_ast.items():
        if k == "loc":
            continue
        if k not in goal2_ast:
            return False
        values_equal = compare_expressions_under_substitution(
            v, goal2_ast[k], one_to_two_mapping, avail_names_two)
        if not values_equal:
            return False
    return True


def __compare_qualid_under_substitution(
        exp1_ast: list[Any],
        exp2_ast: list[Any],
        one_to_two_mapping: dict[str, Optional[str]],
        avail_names_two: set[str]) -> bool:
    assert exp1_ast[0] == "Ser_Qualid"
    qual1 = CoqQualId.from_json(exp1_ast)
    try:
        qual2 = CoqQualId.from_json(exp2_ast)
    except AssertionError:
        return False

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
        avail_names_two: set[str]) -> bool:
    assert exp1_ast[0] == "Name"
    name1 = CoqName.from_json(exp1_ast)
    try:
        name2 = CoqName.from_json(exp2_ast)
    except AssertionError:
        return False
    assert name1.id not in one_to_two_mapping
    assert name2.id not in avail_names_two
    avail_names_two.add(name2.id)
    one_to_two_mapping[name1.id] = name2.id
    return True


def __compare_lists_under_substitution(
        exp1_ast: list[Any],
        exp2_ast: Any,
        one_to_two_mapping: dict[str, Optional[str]],
        avail_names_two: set[str]) -> bool:
    assert type(exp1_ast) == list
    if type(exp2_ast) != list:
        return False
    if len(exp1_ast) == 0:
        return len(exp2_ast) == 0
    if exp1_ast[0] == "Ser_Qualid":
        return __compare_qualid_under_substitution(
            exp1_ast, exp2_ast, one_to_two_mapping, avail_names_two)
    if exp1_ast[0] == "Name":
        return __compare_names_under_substitution(
            exp1_ast, exp2_ast, one_to_two_mapping, avail_names_two)
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
            exp1_el, exp2_el, one_to_two_mapping, avail_names_two)
        if not expr_eq:
            return False
    return True


    
def compare_expressions_under_substitution(
        exp1_ast: Any, exp2_ast: Any, 
        one_to_two_mapping: dict[str, Optional[str]],
        avail_names_two: set[str]) -> bool:
    if type(exp1_ast) == dict:
        return __compare_dicts_under_substitution(
            exp1_ast, exp2_ast, one_to_two_mapping, avail_names_two)

    if type(exp1_ast) == list:
        return __compare_lists_under_substitution(
            exp1_ast, exp2_ast, one_to_two_mapping, avail_names_two)
        
    if exp1_ast is None and exp2_ast is None:
        return True
    try:
        assert (type(exp1_ast) == str or
                type(exp1_ast) == int)
        assert (type(exp2_ast) == str or
                type(exp2_ast) == int)
        return exp1_ast == exp2_ast 
    except AssertionError:
        pdb.set_trace()
    return False


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


def run_test() -> None:
    from coqlspclient.coq_file import CoqFile
    test_file1 = "/home/ubuntu/coq-modeling/test-coq-projs/test1.v"
    with CoqFile(test_file1, timeout=60) as coq_file:
        ast1 = extract_last_definition_body(coq_file.ast)
    test_file2 = "/home/ubuntu/coq-modeling/test-coq-projs/test2.v"
    with CoqFile(test_file2, timeout=60) as coq_file:
        ast2 = extract_last_definition_body(coq_file.ast)
    one_to_two_mapping: dict[str, Optional[str]] = {}
    two_name_set: set[str] = set()
    #pdb.set_trace()
    print(compare_expressions_under_substitution(
        ast1, ast2, one_to_two_mapping, two_name_set))
    print(one_to_two_mapping)
    print(two_name_set)


    # exp1 = {"a": [1, 2, {"b": [3, {"f": [4, 5, 6]}, 5]}]}
    # exp2 = {"a": [1, 2, {"b": [3, {"f": [4, 5, 6]}, 5]}]}
    # print(compare_expressions_under_substitution(exp1, exp2, {}, set()))


if __name__ == "__main__":
    run_test()