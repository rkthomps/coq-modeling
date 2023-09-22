
from __future__ import annotations
from coqlspclient.coq_lsp_structs import Goal


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

    def same_as(self, other: Obligation) -> bool:
        return self.as_hard_as(other) and (len(self.goal.hyps) == len(other.goal.hyps))


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

