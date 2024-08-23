import os
import shutil
import subprocess

from data_management.create_file_data_point import get_data_point, get_switch_loc
from data_management.sentence_db import SentenceDB
from data_management.splits import DATA_POINTS_NAME, REPOS_NAME
from test_utils.utils import (
    LIST_DEFS_LOC,
    LIST_THMS_LOC,
    TEST_PROJET_LOC,
    TEST_MINI_DATASET_LOC,
    TEST_MINI_DATASET_SENTENCE_DB,
)


def setup_project_dataset():
    if TEST_MINI_DATASET_LOC.exists():
        shutil.rmtree(TEST_MINI_DATASET_LOC)

    os.makedirs(TEST_MINI_DATASET_LOC / DATA_POINTS_NAME)
    os.makedirs(TEST_MINI_DATASET_LOC / REPOS_NAME)

    sentence_db_loc = TEST_MINI_DATASET_SENTENCE_DB
    sentence_db = SentenceDB.create(sentence_db_loc)

    workspace_loc = TEST_MINI_DATASET_LOC / REPOS_NAME / TEST_PROJET_LOC.name
    shutil.copytree(TEST_PROJET_LOC, workspace_loc)

    # orig_dir = os.getcwd()
    # os.chdir(workspace_loc)
    # subprocess.run(["make", "clean"])
    # subprocess.run(["make"])
    # os.chdir(orig_dir)

    list_defs_loc = workspace_loc / (LIST_DEFS_LOC.relative_to(TEST_PROJET_LOC))
    list_thms_loc = workspace_loc / (LIST_THMS_LOC.relative_to(TEST_PROJET_LOC))

    print(list_defs_loc)
    print(list_thms_loc)

    defs_dp = get_data_point(
        list_defs_loc, workspace_loc, sentence_db, True, get_switch_loc()
    )
    thms_dp = get_data_point(
        list_thms_loc, workspace_loc, sentence_db, True, get_switch_loc()
    )

    defs_dp.save(
        TEST_MINI_DATASET_LOC / DATA_POINTS_NAME / defs_dp.dp_name,
        sentence_db,
        insert_allowed=True,
    )
    thms_dp.save(
        TEST_MINI_DATASET_LOC / DATA_POINTS_NAME / thms_dp.dp_name,
        sentence_db,
        insert_allowed=True,
    )
