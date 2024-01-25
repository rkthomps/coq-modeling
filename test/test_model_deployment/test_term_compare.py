from model_deployment.term_compare import app_p, AppT, VarT


class TestTermCompare:
    def test_assoc(self) -> None:
        str1 = "a b"
        res1 = app_p.parse(str1)
        assert res1 == AppT(VarT("a"), [VarT("b")])
        str2 = "a b c"
        res2 = app_p.parse(str2)
        assert res2 == AppT(VarT("a"), [VarT("b"), VarT("c")])
