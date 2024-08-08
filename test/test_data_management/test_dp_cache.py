import os
from pathlib import Path
from data_management.dataset_file import DatasetFile, FileContext, Proof, DPCache
from data_management.sentence_db import SentenceDB
from util.constants import DATA_POINTS_NAME

DATA_LOC = Path("raw-data/coq-dataset")
SENTENCE_DB_LOC = Path("raw-data/coq-dataset/sentences.db")


class TestDPCache:
    def test_cache_overflow(self):
        if DATA_LOC.exists() and SENTENCE_DB_LOC.exists():
            cache = DPCache(cache_size=2)
            data_points_loc = DATA_LOC / DATA_POINTS_NAME
            sentence_db = SentenceDB.load(SENTENCE_DB_LOC)
            for dp_name in os.listdir(data_points_loc)[:30]:
                dp = DatasetFile.load(data_points_loc / dp_name, sentence_db)
                cached_dp = cache.get_dp(dp_name, DATA_LOC, sentence_db)
                assert cached_dp.dp_name == dp.dp_name
