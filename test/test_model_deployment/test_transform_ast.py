from model_deployment.transform_ast import StrTree


class TestTransformAst:
    def test1(self) -> None:
        t1 = StrTree("1", [])
        t2 = StrTree("1", [])
        assert t1.distance(t2) == 0

    def test2(self) -> None:
        t1 = StrTree("1", [StrTree("2", []), StrTree("3", [])])
        t2 = StrTree("1", [StrTree("2", []), StrTree("3", [])])
        assert t1.distance(t2) == 0

    def test3(self) -> None:
        t1 = StrTree("1", [StrTree("2", []), StrTree("3", [])])
        t2 = StrTree("1", [StrTree("3", []), StrTree("2", [])])
        assert t1.distance(t2) == 1
        assert t2.distance(t1) == 1

    def test4(self) -> None:
        t1 = StrTree("1", [StrTree("2", []), StrTree("3", [])])
        t2 = StrTree("1", [StrTree("2", []), StrTree("3", []), StrTree("4", [])])
        assert t1.distance(t2) == 1
        assert t2.distance(t1) == 1

    def test5(self) -> None:
        t1 = StrTree("1", [StrTree("2", []), StrTree("3", [])])
        t2 = StrTree("1", [StrTree("3", []), StrTree("2", []), StrTree("4", [])])
        assert t1.distance(t2) == 2
        assert t2.distance(t1) == 2

    def test6(self) -> None:
        t1 = StrTree("1", [StrTree("2", []), StrTree("3", [])])
        t2 = StrTree("0", [StrTree("1", [StrTree("2", []), StrTree("3", [])])])
        assert t1.distance(t2) == 1
        assert t2.distance(t1) == 1

    def test7(self) -> None:
        t1 = StrTree("1", [StrTree("2", []), StrTree("3", [])])
        t2 = StrTree(
            "0", [StrTree("2", []), StrTree("1", [StrTree("2", []), StrTree("3", [])])]
        )
        assert t1.distance(t2) == 2
        assert t2.distance(t1) == 2

    def test8(self) -> None:
        t = StrTree(
            "0", [StrTree("2", []), StrTree("1", [StrTree("2", []), StrTree("3", [])])]
        )
        assert t.keyset() == ["0", "1", "2", "2", "3"]
