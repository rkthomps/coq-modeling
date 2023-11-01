import unittest

from tactic_gen.step_parser import (
    IdTok,
    SpecialToken,
    CommentTok,
    PatternTok,
    ExprTok,
    lex,
    normalize,
    tokens2str,
    ID_HOLE,
    EXPR_HOLE,
    STRING_HOLE,
)


class StepParserCase(unittest.TestCase):
    def test_lex_easy_step(self) -> None:
        exp = [IdTok("intros"), SpecialToken.PERIOD]
        act = lex("intros.")
        self.assertEqual(exp, act)

    def test_lex_comment(self) -> None:
        exp = [IdTok("intros"), CommentTok(" this is a comment "), SpecialToken.PERIOD]
        act = lex("intros  (* this is a comment *) .")
        self.assertEqual(exp, act)

    def test_lex_inversion(self) -> None:
        exp = [
            IdTok("inversion"),
            IdTok("H"),
            IdTok("as"),
            PatternTok(
                [SpecialToken.OR_DISJUNCT, IdTok("ns"), IdTok("IHn"), IdTok("Eq")]
            ),
            SpecialToken.PERIOD,
        ]
        act = lex("inversion H as [ | ns IHn Eq ].")
        self.assertEqual(exp, act)

    def test_focus1(self) -> None:
        exp = [SpecialToken.DASH]
        act = lex("- ")
        self.assertEqual(exp, act)

    def test_assert(self) -> None:
        exp = [
            IdTok("assert"),
            ExprTok(
                [
                    IdTok("forall"),
                    IdTok("n"),
                    SpecialToken.COMMA,
                    IdTok("embed"),
                    IdTok("xy"),
                    IdTok("="),
                    IdTok("n"),
                    IdTok("->"),
                    IdTok("unembed"),
                    IdTok("n"),
                    IdTok("="),
                    IdTok("xy"),
                ]
            ),
            SpecialToken.PERIOD,
        ]
        act = lex(" assert (forall n, embed xy = n -> unembed n = xy).")
        self.assertEqual(exp, act)

    def test_lex_id_with_semicolon(self) -> None:
        exp = [
            IdTok("case"),
            IdTok("x"),
            IdTok("as"),
            PatternTok([SpecialToken.OR_DISJUNCT, IdTok("x")]),
            SpecialToken.SEMICOLON,
            IdTok("intro"),
            IdTok("Hx"),
            SpecialToken.SEMICOLON,
            IdTok("rewrite"),
            SpecialToken.LEFT_ARROW,
            IdTok("Hx"),
            SpecialToken.SEMICOLON,
            IdTok("simpl"),
            SpecialToken.PERIOD,
        ]
        act = lex(" case x as [|x]; intro Hx; rewrite <- Hx; simpl.")
        self.assertEqual(exp, act)

    def test_lex_lia_rewrite(self) -> None:
        exp = [
            IdTok("rewrite"),
            SpecialToken.LEFT_ARROW,
            ExprTok([IdTok("Z2Nat.id"), IdTok("n")]),
            IdTok("in"),
            IdTok("H0"),
            IdTok("by"),
            IdTok("lia"),
            SpecialToken.PERIOD,
        ]
        act = lex(" rewrite <- (Z2Nat.id n) in H0 by lia.")
        self.assertEqual(exp, act)

    def test_lex_bar_dash_notation(self) -> None:
        exp = [
            IdTok("simpl"),
            IdTok("in"),
            IdTok("H"),
            SpecialToken.ENTAIL_TOK,
            SpecialToken.STAR,
            SpecialToken.PERIOD,
        ]
        act = lex("simpl in H |- *.")
        self.assertEqual(exp, act)

    def test_lex_destruct(self) -> None:
        exp = [
            IdTok("destruct"),
            IdTok("al"),
            SpecialToken.SEMICOLON,
            PatternTok(
                [
                    IdTok("rewrite"),
                    IdTok("skipn_nil"),
                    SpecialToken.SEMICOLON,
                    IdTok("auto"),
                    SpecialToken.OR_DISJUNCT,
                ]
            ),
            SpecialToken.PERIOD,
        ]
        act = lex("  destruct al; [ rewrite skipn_nil; auto | ].  ")
        self.assertEqual(exp, act)

    def test_lex_match(self) -> None:
        exp = [
            IdTok("destruct"),
            IdTok("match"),
            IdTok("n"),
            IdTok("with"),
            SpecialToken.OR_DISJUNCT,
            IdTok("O"),
            IdTok("=>"),
            IdTok("S"),
            IdTok("m"),
            SpecialToken.OR_DISJUNCT,
            IdTok("S"),
            IdTok("l"),
            IdTok("=>"),
            ExprTok([IdTok("m"), IdTok("-"), IdTok("l")]),
            IdTok("%nat"),
            IdTok("end"),
            SpecialToken.SEMICOLON,
            IdTok("reflexivity"),
            SpecialToken.PERIOD,
        ]
        act = lex(
            " destruct match n with\n    | O => S m\n    | S l => (m - l)%nat end; reflexivity."
        )
        self.assertEqual(exp, act)

    def test_lex_funky_expr(self) -> None:
        exp = [
            IdTok("replace"),
            ExprTok([IdTok("hi-lo")]),
            IdTok("with"),
            ExprTok(
                [
                    ExprTok([IdTok("mid-lo")]),
                    IdTok("+"),
                    ExprTok([IdTok("hi-mid")]),
                ]
            ),
            IdTok("by"),
            IdTok("lia"),
            SpecialToken.PERIOD,
        ]
        act = lex("replace (hi-lo) with ((mid-lo)+(hi-mid)) by lia.")
        self.assertEqual(exp, act)

    def test_lex_assert_2(self) -> None:
        exp = [
            IdTok("assert"),
            ExprTok(
                [
                    IdTok("Zlength"),
                    ExprTok(
                        [
                            IdTok("skipn"),
                            ExprTok(
                                [
                                    IdTok("Z.to_nat"),
                                    IdTok("lo"),
                                ]
                            ),
                            IdTok("l"),
                        ]
                    ),
                    IdTok("<"),
                    IdTok("hi"),
                    IdTok("-"),
                    IdTok("lo"),
                ]
            ),
            SpecialToken.SEMICOLON,
            PatternTok(
                [
                    SpecialToken.OR_DISJUNCT,
                    IdTok("rewrite"),
                    IdTok("Z.min_r"),
                    SpecialToken.SEMICOLON,
                    IdTok("lia"),
                ]
            ),
            SpecialToken.PERIOD,
        ]
        act = lex(
            "  assert (Zlength (skipn (Z.to_nat lo) l) < hi - lo); [| rewrite Z.min_r; lia].  "
        )
        self.assertEqual(exp, act)

    def test_whacky_destruct(self) -> None:
        exp = [
            IdTok("destruct"),
            IdTok("H4"),
            IdTok("as"),
            PatternTok(
                [
                    IdTok("?"),
                    PatternTok(
                        [
                            IdTok("??"),
                        ]
                    ),
                ]
            ),
            SpecialToken.PERIOD,
        ]
        act = lex(" destruct H4 as [?[??]].")
        self.assertEqual(exp, act)

    def test_lex_set_expr(self) -> None:
        exp = [
            IdTok("set"),
            ExprTok(
                [
                    IdTok("N2B"),
                    ExprTok(
                        [
                            IdTok("n"),
                            SpecialToken.COLON,
                            IdTok("Nat"),
                        ]
                    ),
                    SpecialToken.ASSIGN,
                    IdTok("match"),
                    IdTok("n"),
                    IdTok("with"),
                    SpecialToken.OR_DISJUNCT,
                    IdTok("succ"),
                    IdTok("n'"),
                    IdTok("=>"),
                    IdTok("true"),
                    SpecialToken.OR_DISJUNCT,
                    IdTok("zero"),
                    IdTok("=>"),
                    IdTok("false"),
                    IdTok("end"),
                ]
            ),
            SpecialToken.PERIOD,
        ]
        act = lex(
            "set (N2B (n : Nat) := match n with | succ n' => true | zero => false end)."
        )
        self.assertEqual(exp, act)

    def test_lex_eqn(self) -> None:
        exp = [
            IdTok("destruct"),
            IdTok("l"),
            IdTok("as"),
            PatternTok(
                [
                    SpecialToken.OR_DISJUNCT,
                    IdTok("h"),
                    IdTok("l'"),
                ]
            ),
            IdTok("eqn"),
            SpecialToken.COLON,
            IdTok("E"),
            SpecialToken.PERIOD,
        ]
        act = lex("destruct l as [|h l'] eqn:E.")
        self.assertEqual(exp, act)

    def test_norm_inversion(self) -> None:
        exp = [
            IdTok("inversion"),
            IdTok(ID_HOLE),
            IdTok("as"),
            PatternTok(
                [
                    SpecialToken.OR_DISJUNCT,
                    IdTok(ID_HOLE),
                    IdTok(ID_HOLE),
                    IdTok(ID_HOLE),
                ]
            ),
            SpecialToken.PERIOD,
        ]
        act = normalize(lex("inversion H as [ | ns IHn Eq ]."))
        self.assertEqual(exp, act)

    def test_tok_2_str(self) -> None:
        exp = "inversion H as [ | ns IHn Eq ] ."
        act = tokens2str(lex("inversion H as [ | ns IHn Eq ]."))
        self.assertEqual(exp, act)

    def test_norm_tok_2_str(self) -> None:
        exp = f"inversion {ID_HOLE} as [ | {ID_HOLE} {ID_HOLE} {ID_HOLE} ] ."
        act = tokens2str(normalize(lex("inversion H as [ | ns IHn Eq ].")))
        self.assertEqual(exp, act)

    def test_norm_tok_2_str_2(self) -> None:
        exp = f"assert {EXPR_HOLE} ; [ | rewrite {ID_HOLE} ; lia ] ."
        act = tokens2str(
            normalize(
                lex(
                    "  assert (Zlength (skipn (Z.to_nat lo) l) < hi - lo); [| rewrite Z.min_r; lia].  "
                )
            )
        )
        self.assertEqual(exp, act)

    def test_goofy_to_str(self) -> None:
        exp = f"assert {EXPR_HOLE} ; rewrite {STRING_HOLE} ."
        act = tokens2str(normalize(lex('assert (); rewrite "hello".')))
        self.assertEqual(exp, act)

    def test_arrow_to_str(self) -> None:
        exp = f"rewrite -> {ID_HOLE} ."
        act = tokens2str(normalize(lex("rewrite -> add_assoc.")))
        self.assertEqual(exp, act)


if __name__ == "__main__":
    runner = unittest.TextTestRunner()
    suite = unittest.TestSuite()
    suite.addTest(StepParserCase("test_lex_set_expr"))
    runner.run(suite)
