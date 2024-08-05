import sys
import os
import argparse
import json
import pexpect
import time
import tqdm
import logging

from pathlib import Path
from util.file_queue import FileQueue, EmptyFileQueueError
from data_management.dataset_file import DatasetFile, Proof
from data_management.splits import DataSplit, FileInfo
from data_management.sentence_db import SentenceDB


DATA_PREFIX = Path("../../raw-data/coq-dataset/")
REPOS_LOC = DATA_PREFIX / "repos"
RESULTS_LOC = Path("results/")
PREFIX_LOC = Path("prefixes")


class CoqTop:
    def __init__(
        self,
        file: str,
        timeout: int = 10,
        workdir: str | None = None,
        options: str = "",
    ):
        self.process = pexpect.spawn(
            f"tactician exec -- coqtop -load-vernac-source {file} {options}",
            encoding="utf-8",
            timeout=timeout,
            cwd=workdir,
        )
        try:
            self.process.expect("([a-zA-z1-9_][^\n]*?) < ")
        except Exception as e:
            self.process.kill(9)
            raise e

    def run(self, command: str, expect: str = "([a-zA-z1-9_][^\n]*?) < "):
        self.process.write(command + "\n")
        self.process.expect(expect)
        return self.process.before

    def kill(self):
        self.process.kill(9)


def test_proof(
    coq_file_loc: Path,
    project: str,
    original_file: str,
    thm: str,
):
    new_path = (DATA_PREFIX / original_file).parent / coq_file_loc.name
    print(f"Going to prove: {new_path}")
    with coq_file_loc.open("r") as fin:
        proof_text = fin.readlines()

    with open(new_path, "w") as fout:
        fout.writelines(proof_text[:-2])  # Without Qed and synth.

    assert os.path.exists(new_path)

    workspace = REPOS_LOC / project
    if os.path.exists(workspace / "_CoqProject"):
        with open(workspace / "_CoqProject", "r") as f:
            for line in f.readlines():
                if line.startswith("-"):
                    options = line
                    break
    else:
        options = ""

    start = time.time()
    try:
        coq_top = CoqTop(
            str(new_path.resolve()), timeout=60 * 10, workdir=workspace, options=options
        )
    except Exception as e:
        logging.warning(f"Failed to compile {new_path}: {e}")
        os.remove(new_path)
        return
    compile_time = time.time() - start

    start = time.time()
    try:
        stdout = coq_top.run("all: synth.", expect="Tactician found a proof!")
        stdout += coq_top.process.after
        coq_top.process.expect("([a-zA-z1-9_][^\n]*?) < ")
        stdout += coq_top.process.before
        timeout = False
    except pexpect.exceptions.TIMEOUT:
        stdout = ""
        timeout = True
    except pexpect.exceptions.EOF:
        stdout = ""
        timeout = False

    synth_time = time.time() - start
    coq_top.kill()

    success = "Tactician found a proof!" in stdout

    print(success)
    print(stdout)
    with (RESULTS_LOC / coq_file_loc.name).open("w") as fout:
        fout.write(
            json.dumps(
                {
                    "file": original_file,
                    "compile_time": compile_time,
                    "synth_time": synth_time,
                    "theorem": thm,
                    "success": success,
                    "timeout": timeout,
                    "stdout": stdout,
                },
                indent=2,
            )
        )

    os.remove(new_path)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("queue_loc", help="Location of the queue.")

    args = parser.parse_args(sys.argv[1:])
    file_queue = FileQueue(Path(args.queue_loc))

    while True:
        try:
            coq_file_loc, project, original_file, thm = file_queue.get()
            save_loc = RESULTS_LOC / coq_file_loc.name
            if save_loc.exists():
                print(f"Skipping {coq_file_loc.name}. Already processed.")
                continue
            print(f"Processing proof {coq_file_loc.name}")
            test_proof(coq_file_loc, project, original_file, thm)
        except EmptyFileQueueError:
            break

    # prefix_files = ["coq-contribs-zfc-38.json"]

    # for prefix_file in prefix_files:
    #     # for prefix_file in os.listdir(PREFIX_LOC):
    #     if not prefix_file.endswith(".json"):
    #         continue
    #     data_loc = PREFIX_LOC / prefix_file
    #     coq_file_loc = data_loc.with_suffix(".v")

    #     with data_loc.open() as fin:
    #         file_data = json.load(fin)
    #         project = file_data["project"]
    #         file = file_data["file"]
    #         thm = file_data["thm"]

    #     test_proof(coq_file_loc, project, file, thm)
