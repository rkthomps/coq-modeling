import unittest
from test_model_deployment.test_goal_comparer import GoalComparerTestCase
from test_model_deployment.test_node_score import NodeScoreTestCase


def suite() -> unittest.TestSuite:
    suite = unittest.TestSuite()
    # Goal Comparison
    suite.addTest(GoalComparerTestCase("test_equiv_goals"))
    suite.addTest(GoalComparerTestCase("test_harder_goals"))
    suite.addTest(GoalComparerTestCase("test_non_comparable_goals"))
    suite.addTest(GoalComparerTestCase("test_inversion"))
    suite.addTest(GoalComparerTestCase("test_compare_expressions"))

    # Node Scoring
    suite.addTest(NodeScoreTestCase("touch_everything_test"))
    return suite


if __name__ == "__main__":
    runner = unittest.TextTestRunner()
    runner.run(suite())
