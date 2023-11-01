import unittest
from test_model_deployment.test_goal_comparer import GoalComparerTestCase
from test_model_deployment.test_node_score import NodeScoreTestCase
from test_tactic_gen.test_step_parser import StepParserCase


def suite() -> unittest.TestSuite:
    suite = unittest.TestSuite()

    cases: list[type[unittest.TestCase]] = [
        GoalComparerTestCase,
        NodeScoreTestCase,
        StepParserCase,
    ]

    for case in cases:
        tests_from_case = unittest.defaultTestLoader.loadTestsFromTestCase(case)
        suite.addTests(tests_from_case)
    return suite


if __name__ == "__main__":
    runner = unittest.TextTestRunner()
    runner.run(suite())
