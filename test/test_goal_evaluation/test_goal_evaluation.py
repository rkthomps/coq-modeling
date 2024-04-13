
from goal_evaluation.goal_example import GoalExample, GoalFormatter
from data_management.dataset_file import Proof, Term, Step, FocusedStep, DatasetFile, FileContext
from coqpyt.coq.structs import TermType

class TestGoalEvaluation:
    def test_goal1(self):
        t = Term.from_text("hi bob.", TermType.LEMMA)
        s = FocusedStep(t, Step("Qed.", []), 0, [])
        p = Proof(t, [s])
        exp_example = GoalExample("", 1)
        assert GoalFormatter().example_from_step(0, p) == exp_example