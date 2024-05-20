
import os
from pathlib import Path
import subprocess

MINI_TEST_PROJET_LOC = Path("test/test_files/mini-coq-project")

def build_mini_test_project():
    orig_dir = Path(os.curdir)
    try:
        os.chdir(MINI_TEST_PROJET_LOC)
        subprocess.run("make")
    finally:
        os.chdir(orig_dir)

