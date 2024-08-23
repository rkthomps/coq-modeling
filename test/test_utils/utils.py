import os
from pathlib import Path
import subprocess

from data_management.sentence_db import SentenceDB

TEST_PROJET_LOC = Path("test/test_files/test-project")
TEST_FILES_LOC = Path("test/test_files")
TEST_TMP_LOC = Path("test/test_files/tmp")

TEST_MINI_DATASET_LOC = TEST_FILES_LOC / "mini-dataset"
TEST_MINI_DATASET_SENTENCE_DB = TEST_MINI_DATASET_LOC / "sentences.db"
LIST_DEFS_DP = "test-project-theories-ListDefs.v"
LIST_THMS_DP = "test-project-theories-ListThms.v"

LIST_DEFS_LOC = TEST_PROJET_LOC / "theories" / "ListDefs.v"
LIST_THMS_LOC = TEST_PROJET_LOC / "theories" / "ListThms.v"

SENTENCE_DB_LOC = TEST_TMP_LOC / "sentences.db"


def build_test_project():
    orig_dir = Path(os.curdir).resolve()
    try:
        os.chdir(TEST_PROJET_LOC)
        subprocess.run("make")
    finally:
        os.chdir(orig_dir)


def get_test_sentence_db():
    if SENTENCE_DB_LOC.exists():
        os.remove(SENTENCE_DB_LOC)
    os.makedirs(SENTENCE_DB_LOC.parent, exist_ok=True)
    sentence_db = SentenceDB.create(SENTENCE_DB_LOC)
    return sentence_db
