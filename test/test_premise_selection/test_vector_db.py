import hashlib
import torch
import shutil
import os

from util.util import get_fresh_path

from data_management.sentence_db import SentenceDB, DBSentence
from premise_selection.premise_vector_db import PremiseVectorDB


def encode_fn(db_ss: list[DBSentence]) -> torch.Tensor:
    hashs: list[list[int]] = []
    for dbs in db_ss:
        m = hashlib.sha256()
        m.update(dbs.text.encode())
        m_hash = list(m.digest())
        hashs.append(m_hash)
    return torch.tensor(hashs)


def get_ordered_sentences(ss: list[DBSentence], db_idxs: list[int]) -> list[DBSentence]:
    ordered: list[DBSentence] = []
    for idx in db_idxs:
        ordered.append(ss[idx - 1])
    return ordered


class TestVectorDB:
    def test_retrieve1(self):
        vdb = PremiseVectorDB.load(self.vdb_loc)
        exp = encode_fn(self.test_sentences)
        act = vdb.get_embs([1, 2, 3, 4, 5])
        assert act is not None
        assert torch.allclose(act, exp)

    def test_retrieve2(self):
        vdb = PremiseVectorDB.load(self.vdb_loc)
        idxs = [5, 4, 3, 2, 1]
        exp = encode_fn(get_ordered_sentences(self.test_sentences, idxs))
        act = vdb.get_embs(idxs)
        assert act is not None
        assert torch.allclose(act, exp)

    def test_retrieve3(self):
        vdb = PremiseVectorDB.load(self.vdb_loc)
        idxs = [5, 3, 3, 4, 3, 1, 1, 2, 1]
        exp = encode_fn(get_ordered_sentences(self.test_sentences, idxs))
        act = vdb.get_embs(idxs)
        assert act is not None
        assert torch.allclose(act, exp)

    @classmethod
    def setup_class(cls) -> None:
        cls.sdb_loc = get_fresh_path(".", "test_sdb")
        cls.test_sentences = [
            DBSentence("hi", "", "", "", 0),
            DBSentence("there", "", "", "", 0),
            DBSentence("guy", "", "", "", 0),
            DBSentence("bob", "", "", "", 0),
            DBSentence("steuart", "", "", "", 0),
        ]
        sdb = SentenceDB.create(cls.sdb_loc)
        for ts in cls.test_sentences:
            sdb.insert_sentence(ts)

        cls.vdb_loc = get_fresh_path(".", "test_vdb")
        vdb = PremiseVectorDB.create(
            cls.vdb_loc, 2, "test_vector_db", encode_fn, cls.sdb_loc
        )
        vdb.save()

    @classmethod
    def teardown_class(cls) -> None:
        if os.path.exists(cls.sdb_loc):
            os.remove(cls.sdb_loc)
        if os.path.exists(cls.vdb_loc):
            shutil.rmtree(cls.vdb_loc)
