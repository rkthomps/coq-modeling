import unittest
import pdb

from data_management.dataset_file import FocusedStep, Goal
from tactic_gen.tactic_pair_encoding import TacticPairEncoding
from tactic_gen.n_step_sampler import NStepTPESampler, NStepResult
from tactic_gen.step_parser import normalize, tokens2str, lex


class NStepSamplerCase(unittest.TestCase):
    def test_tpe_sampler_1(self):
        norm_intros = tokens2str(normalize(lex("intros.")))
        norm_destruct = tokens2str(normalize(lex("destruct.")))
        fs1 = FocusedStep.from_step_text("intros.")
        fs2 = FocusedStep.from_step_text("induction.")
        fs3 = FocusedStep.from_step_text("destruct.")

        tpe = TacticPairEncoding(
            {
                norm_intros: 1,
                norm_destruct: 2,
                TacticPairEncoding.merge_steps([norm_intros, norm_destruct]): 3,
            }
        )

        sampler = NStepTPESampler(tpe)

        exp1 = NStepResult([fs2], fs1.goals)
        act1 = sampler.sample_steps([fs2, fs1, fs3])

        exp2 = NStepResult([fs2], fs2.goals)
        act2 = sampler.sample_steps([fs2, fs2, fs2])

        exp3 = NStepResult([fs1, fs3], fs3.goals)
        act3 = sampler.sample_steps([fs1, fs3, fs3])

        with self.assertRaises(AssertionError):
            sampler.sample_steps([])

        self.assertEqual(exp1, act1)
        self.assertEqual(exp2, act2)
        self.assertEqual(exp3, act3)
