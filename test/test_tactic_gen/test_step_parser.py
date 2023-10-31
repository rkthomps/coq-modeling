import unittest

from tactic_gen.step_parser import IdTok, SpecialToken, CommentTok, lex


class StepParserCase(unittest.TestCase):
    def test_easy_step(self) -> None:
        exp = [IdTok("intros"), SpecialToken.PERIOD]
        act = lex("intros.")
        self.assertEqual(exp, act)

    def test_comment(self) -> None:
        exp = [IdTok("intros"), CommentTok(" this is a comment "), SpecialToken.PERIOD]
        act = lex("intros  (* this is a comment *) .")
        self.assertEqual(exp, act)
