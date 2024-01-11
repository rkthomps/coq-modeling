from coqpyt.coq.structs import GoalAnswer
from coqpyt.coq.lsp.structs import Goal


def get_all_goals(goal_answer: GoalAnswer) -> list[Goal]:
    assert goal_answer.goals is not None
    collapsed_stack: list[Goal] = []
    for stack_goals1, stack_goals2 in goal_answer.goals.stack:
        collapsed_stack.extend(stack_goals1)
        collapsed_stack.extend(stack_goals2)
    return goal_answer.goals.goals + collapsed_stack + goal_answer.goals.shelf
