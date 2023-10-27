import unittest
from test_model_deployment.goal_comparer import GoalComparerTestCase


def suite() -> unittest.TestSuite:
    suite = unittest.TestSuite()
    suite.addTest(GoalComparerTestCase("test_redundant_hyps"))
    return suite


if __name__ == "__main__":
    runner = unittest.TextTestRunner()
    runner.run(suite())
