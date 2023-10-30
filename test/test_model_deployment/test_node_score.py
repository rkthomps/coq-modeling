import sys, os
import unittest
import json

from model_deployment.proof_manager import get_fresh_path
from model_deployment.node_score import (
    NODE_SCORE_ALIASES,
    NodeScore,
    LastTacGreedyScore,
)


class NodeScoreTestCase(unittest.TestCase):
    def touch_everything_test(self) -> None:
        not_matching = NodeScore()
        for alias, node_score_type in NODE_SCORE_ALIASES.items():
            init_score = node_score_type.get_initial_score(4)
            unit_score = node_score_type.from_unit_score(-2.3, 4, 3)
            comb_score = init_score.agg(unit_score)
            json_init_score = init_score.to_json()
            json_unit_score = unit_score.to_json()
            init_score2 = node_score_type.from_json(json_init_score)
            unit_score2 = node_score_type.from_json(json_unit_score)
            comb_score2 = init_score2.agg(unit_score2)
            self.assertEqual(comb_score.compute(), comb_score2.compute())
            with self.assertRaises(ValueError):
                init_score.agg(not_matching)
