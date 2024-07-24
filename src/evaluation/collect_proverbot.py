import os
import shutil
from pathlib import Path

PROVERBOT_LOC = Path(
    "/project/pi_brun_umass_edu/zhannakaufma/coqgym-dfs-emily-and-alex"
)
SAVE_LOC = Path("evaluations/proverbot/")
os.makedirs(SAVE_LOC, exist_ok=True)


def move_proverbot_results(path: Path):
    for root, _, files in os.walk(path):
        for file in files:
            if file.endswith("-proofs.txt"):
                shutil.copy(Path(root) / file, SAVE_LOC / file)


move_proverbot_results(PROVERBOT_LOC)
