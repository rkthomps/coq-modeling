

import os
import shutil

import pytest

from data_management.sentence_db import DBSentence, SentenceDB


class TestSentenceDB:
    DB_PATH = "the_db"

    def test_duplicate_create(self) -> None:
        with pytest.raises(ValueError):
            SentenceDB.create(self.DB_PATH)
    

    def test_get_id(self) -> None:
        test_sentence1 = DBSentence("hi bob", "hi/bob", "[hi, bob]", "LEMMA", 1)
        result = self.db.find_sentence(test_sentence1)
        assert result == None
        insert1_id = self.db.insert_sentence(test_sentence1)
        find2_id = self.db.find_sentence(test_sentence1)
        assert find2_id == insert1_id 
        retry_insert1_id = self.db.insert_sentence(test_sentence1)
        assert retry_insert1_id == insert1_id
        retrieved_sentence = self.db.retrieve(retry_insert1_id)
        assert retrieved_sentence == test_sentence1

        test_sentence2 = DBSentence("hi bobby", "hi/bob", "[hi, bob]", "LEMMA", 1)
        result2 = self.db.find_sentence(test_sentence2) 
        assert result == None
        insert2_id = self.db.insert_sentence(test_sentence2)
        assert insert2_id != insert1_id
        retrieved_2 = self.db.retrieve(insert2_id)
        assert retrieved_2 == test_sentence2

        retrieved_sentence = self.db.retrieve(retry_insert1_id)
        assert retrieved_sentence == test_sentence1

    @classmethod
    def setup_class(cls) -> None:
        cls.db = SentenceDB.create(cls.DB_PATH)

    @classmethod
    def teardown_class(cls) -> None:
        if os.path.exists(cls.DB_PATH):
            os.remove(cls.DB_PATH)