import sys
import os
import json
import pexpect
import tqdm
import time
import logging

# Avoids error for missing API key
os.environ["OPENAI_API_KEY"] = "PLACEHOLDER"

from pathlib import Path
from data_management.splits import (
    DataSplit, Split, SentenceDB, FileInfo, Proof
)
from concurrent.futures import ThreadPoolExecutor, as_completed


final = DataSplit.load(Path("/home/nfsaavedra/coq-modeling/tactician/cutoff-eval/cutoff-8.18.json"))
random = DataSplit.load(Path("../../splits/random-split.json"))


data_loc = Path("../../raw-data/coq-dataset")
data_points_loc = Path("data-points")
sentence_db_loc = Path("sentences.db")
sentence_db = SentenceDB.load(sentence_db_loc)


results = Path("results/")


class CoqTop:
    def __init__(
        self, 
        file: str, 
        timeout: int = 10, 
        workdir: str | None = None,
        options: str = ""
    ):
        self.process = pexpect.spawn(
            f"coqtop -load-vernac-source {file} {options}", 
            encoding="utf-8",
            timeout=timeout,
            cwd=workdir
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
    proof: Proof,
    file_path: Path, 
    original_file_path: Path, 
    proof_file: Path, 
    file_info: FileInfo, 
    i: int
):
    new_path = Path(os.path.dirname(os.path.realpath(original_file_path))) / f"eval{i}.v"
    with open(proof_file, "r") as f:
        proof_text = f.readlines()

    with open(new_path, "w") as f:
        f.writelines(proof_text)

    workspace = os.path.join(data_loc, file_info.workspace)
    
    if os.path.exists(os.path.join(workspace, "_CoqProject")):
        with open(os.path.join(workspace, "_CoqProject"), "r") as f:
            for line in f.readlines():
                if line.startswith("-"):
                    options = line.split("#")[0]
                    break
    else:
        options = ""

    start = time.time()
    try:
        coq_top = CoqTop(
            new_path, 
            timeout=60 * 10,
            workdir=workspace,
            options=options
        )
    except Exception as e:
        logging.warning(f"Failed to compile {new_path} ({original_file_path}) in workspace {workspace}: {e}")
        os.remove(new_path)
        return
    compile_time = time.time() - start

    start = time.time()
    try:
        stdout = coq_top.run(
            "all: synth.",
            expect="Tactician found a proof!"
        )
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

    with open(results / f"{file_path}_{i}.json", "w") as f:
        f.write(json.dumps({
            "file": file_info.file,
            "compile_time": compile_time,
            "synth_time": synth_time, 
            "theorem": proof.theorem.term.text,
            "success": success,
            "timeout": timeout,
            "stdout": stdout,
        }, indent=2))
    os.remove(new_path)


def tactician_data_points_in_split(
    data_split: DataSplit, split: Split, n_cores: int = 1
):
    pool = ThreadPoolExecutor(n_cores)
    futures = []

    with open('tactician_problems.json', 'r') as f:
        problems = json.loads(f.read())
        problems = list(map(lambda p: p["result_file"], problems))


    for file_info in data_split.get_file_list(split):
        file_path = file_info.file.replace("/", "_")
        file_data_point = file_info.get_dp(data_loc, sentence_db)
        original_file_path = data_loc / file_info.file

        for i, proof in enumerate(file_data_point.proofs):
            if proof.is_proof_independent():
                proof_file = data_points_loc / file_path / f"{i}.v"

                if (
                    not os.path.exists(proof_file)
                    or os.path.exists(results / f"{file_path}_{i}.json")
                    # or not f"{file_path.replace('/', '_')}_{i}.json" in problems
                ):
                    continue

                futures.append(pool.submit(
                    test_proof, 
                    proof, 
                    file_path, 
                    original_file_path, 
                    proof_file, 
                    file_info, 
                    i
                ))

    for future in tqdm.tqdm(as_completed(futures), total=len(futures)):
        future.result()


if __name__ == "__main__":
    if not os.path.exists(results):
        os.makedirs(results)

    if len(sys.argv) > 1:
        n_cores = int(sys.argv[1])
    else:
        n_cores = 1

    tactician_data_points_in_split(final, Split.TEST, n_cores=n_cores)
