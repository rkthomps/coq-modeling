from hypothesis import given, strategies as st, assume

from tactic_gen.proof_distance import levenshtein_dist, levenshtein_dist_fast


class TestProofDistance:
    @given(st.lists(st.text()), st.lists(st.text()))
    def test_lev_eq(self, strs1: list[str], strs2: list[str]) -> None:
        assert levenshtein_dist_fast(strs1, strs2) == levenshtein_dist(strs1, strs2)