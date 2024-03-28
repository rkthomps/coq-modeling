from __future__ import annotations
from coqpyt.coq.structs import Step, RangedSpan
from coqpyt.coq.lsp.structs import Goal, GoalAnswer
from typing import Any, Optional
import ipdb
import re

from typeguard import typechecked

from model_deployment.search_tree import SearchNode
from util.coqpyt_utils import get_all_goals



def goal_as_hard_as(g1: Goal, g2: Goal) -> bool:
    if g1.ty == g2.ty:
        hyp_set_1: set[str] = set([" ".join(h.names) + "; " + h.ty for h in g1.hyps])
        hyp_set_2: set[str] = set([" ".join(h.names) + "; " + h.ty for h in g1.hyps])
        return hyp_set_1.issubset(hyp_set_2)
    return False

def goal_set_as_hard_as(gs1: list[Goal], gs2: list[Goal]) -> bool:
    for g2 in gs2: 
        covered = False
        for g1 in gs1:
            if goal_as_hard_as(g1, g2):
                covered = True
                break
        if not covered:
            return False
    return True

def goal_answer_as_hard_as(ga1: GoalAnswer, ga2: GoalAnswer) -> bool:
    goal_set_1 = get_all_goals(ga1)
    goal_set_2 = get_all_goals(ga2)
    return goal_set_as_hard_as(goal_set_1, goal_set_2)