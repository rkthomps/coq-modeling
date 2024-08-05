import os
from typing import Any
import json
import sys
import shutil
from pathlib import Path
from data_management.splits import DataSplit, Split
from data_management.sentence_db import SentenceDB
from util.file_queue import FileQueue
from subprocess import Popen
import subprocess
import tensorflow as tf
import random


PREFIX_LOC = Path("prefixes")
RESULTS_LOC = Path("results/")

QUEUE_LOC = Path("queue.json")
OUT_LOC = Path("out")


def fill_queue(queue: FileQueue):
    prefix_files = os.listdir(PREFIX_LOC)
    random.shuffle(prefix_files)

    for prefix_file in prefix_files:
        if not prefix_file.endswith(".json"):
            continue
        data_loc = PREFIX_LOC / prefix_file
        coq_file_loc = data_loc.with_suffix(".v")

        with data_loc.open() as fin:
            file_data = json.load(fin)
            project = file_data["project"]
            file = file_data["file"]
            thm = file_data["thm"]

        queue.put((coq_file_loc, project, file, thm))


if __name__ == "__main__":
    if RESULTS_LOC.exists():
        yes_no = input(
            f"Results directory {RESULTS_LOC} already exists. Overwrite (o); Continue (c); Stop (s)? [o/c/s] "
        )
        if yes_no == "s":
            raise FileExistsError(RESULTS_LOC)
        elif yes_no == "c":
            pass
        elif yes_no == "o":
            shutil.rmtree(RESULTS_LOC)
        else:
            raise ValueError(f"Unknown option {yes_no}")

    os.makedirs(RESULTS_LOC, exist_ok=True)
    os.makedirs(OUT_LOC, exist_ok=True)

    if QUEUE_LOC.exists():
        os.remove(QUEUE_LOC)

    queue = FileQueue(QUEUE_LOC)
    queue.initialize()
    fill_queue(queue)
    gpus = tf.config.list_physical_devices("GPU")
    print(f"Executing on {len(gpus)} GPUs:")
    processes: list[Popen[bytes]] = []
    out_files: list[Any] = []
    for i, _ in enumerate(gpus):
        out_file = open(OUT_LOC / ("graph2tac_worker_" + str(i) + ".out"), "w")
        p = Popen(
            [
                "python3",
                "graph2tac_worker.py",
                QUEUE_LOC,
            ],
            env=os.environ | {"CUDA_VISIBLE_DEVICES": str(i)},
            stdout=out_file,
            stderr=subprocess.STDOUT,
        )
        processes.append(p)
        out_files.append(out_file)

    for p, o in zip(processes, out_files):
        p.wait()
        o.close()
