import unittest

from data_management.dataset_file import FocusedStep
from tactic_gen.tactic_pair_encoding import TacticPairEncoding
from tactic_gen.n_step_sampler import NStepTPESampler


class NStepSamplerCase(unittest.TestCase):
    def test_tpe_sampler_1(self):
        fs1 = FocusedStep.from_step_text("hi.")
        fs2 = FocusedStep.from_step_text("bob.")
        fs3 = FocusedStep.from_step_text("gas.")

        tpe = TacticPairEncoding(
            {
                "hi.": 1,
                "gas.": 2,
                TacticPairEncoding.merge_steps(["hi.", "gas."]): 3,
            }
        )

        sampler = NStepTPESampler(tpe)

        exp1 = [[fs2], [fs1, fs3]]
        act1 = sampler.sample_steps([fs2, fs1, fs3])

        exp2 = [[fs2], [fs2], [fs2]]
        act2 = sampler.sample_steps([fs2, fs2, fs2])

        exp3 = [[fs1], [fs1, fs3]]
        act3 = sampler.sample_steps([fs1, fs1, fs3])

        exp4: list[list[FocusedStep]] = []
        act4 = sampler.sample_steps([])

        self.assertEqual(exp1, act1)
        self.assertEqual(exp2, act2)
        self.assertEqual(exp3, act3)
        self.assertEqual(exp4, act4)
