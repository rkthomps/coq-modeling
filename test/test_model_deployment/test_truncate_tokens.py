from pathlib import Path
import pytest
from model_deployment.tactic_gen_client import truncate_lines
import tiktoken

from hypothesis import given, strategies as st


class TestNumTokens:

    def helper(self, text: str, max_tokens: int):
        truncated_text = truncate_lines(self.tokenizer, text, max_tokens)
        num_tokens = len(self.tokenizer.encode(truncated_text))
        assert num_tokens <= max_tokens
        lines = text.split("\n")
        truncated_lines = truncated_text.split("\n")
        num_excluded_lines = len(lines) - len(truncated_lines)
        if 0 < num_excluded_lines:
            truncated_plus_one = "\n".join(lines[(num_excluded_lines - 1) :])
            num_tokens_truncated_plus_one = len(
                self.tokenizer.encode(truncated_plus_one)
            )
            assert max_tokens < num_tokens_truncated_plus_one

    @given(st.integers(min_value=1))
    def test_truncate_lines(self, max_tokens: int):
        self.helper(self.test_str, max_tokens)

    @classmethod
    def setup_class(cls):
        text = Path("test/test_files/harry-potter.txt").read_text()
        cls.test_str = "\n".join(text.split("\n")[:100])
        cls.tokenizer = tiktoken.get_encoding("o200k_base")

    @classmethod
    def teardown_class(cls):
        pass


if __name__ == "__main__":
    TestNumTokens.setup_class()
    TestNumTokens().test_truncate_lines()
    TestNumTokens.teardown_class()
