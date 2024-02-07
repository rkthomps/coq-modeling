from evaluation.step_eval import StepAttempt


class TestStepEval:
    def test_1(self) -> None:
        attempt = StepAttempt(
            "foo",
            ["bar  baz"],
            ["bar  ", "baz"],
            ["foo", "bar  ", "baz"],
        )
        assert attempt.is_correct_at_k(0)
