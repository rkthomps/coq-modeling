import sys, os
import argparse
from pathlib import Path
import subprocess

from datetime import datetime

from util.file_queue import FileQueue
from util.constants import TMP_LOC, QUEUE_NAME


WORKER_SBATCH_LOC = Path("slurm/jobs/compile-worker.sh")


def init_and_fill_queue(queue_loc: Path, repos_loc: Path):
    f = FileQueue[Path](queue_loc)
    f.initialize()
    for repo_name in os.listdir(repos_loc):
        f.put(repos_loc / repo_name)


def start_workers(
    timeout: str,
    n_workers: int,
    n_threads_per_worker: int,
    queue_loc: Path,
):
    worker_sbatch = (
        "#!/bin/bash\n"
        f"#SBATCH -p cpu\n"
        f"#SBATCH -c {n_threads_per_worker}\n"
        f"#SBATCH -t {timeout}\n"
        f"#SBATCH --array=0-{n_workers - 1}\n"
        f"#SBATCH --mem=16G\n"
        f"#SBATCH -o slurm/out/slurm-compile-%j.out\n"
        f"#SBATCH --job-name=COMPILE\n"
        f"source venv/bin/activate\n"
        f"LOG_LEVEL=DEBUG python3 src/data_management/compile_worker.py {queue_loc} {n_threads_per_worker}\n"
    )

    with WORKER_SBATCH_LOC.open("w") as fout:
        fout.write(worker_sbatch)

    # Start proof workers
    subprocess.run(["sbatch", f"{WORKER_SBATCH_LOC}"])


def run(
    repos_loc: Path,
    timeout: str,
    n_workers: int,
    n_threads_per_worker: int,
):
    time_str = datetime.now().strftime("%m%d%H%M%S")
    queue_loc = TMP_LOC / (QUEUE_NAME + "-" + time_str)
    init_and_fill_queue(queue_loc, repos_loc)
    start_workers(
        timeout,
        n_workers,
        n_threads_per_worker,
        queue_loc,
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--repos_loc", help="Path to repositories directory.")
    parser.add_argument("--timeout", help="Timeout for compilation")
    parser.add_argument("--n_workers", type=int, help="Number of workers to use.")
    parser.add_argument(
        "--n_threads_per_worker", type=int, help="Number of threads per worker."
    )

    args = parser.parse_args(sys.argv[1:])
    repos_loc = Path(args.repos_loc)
    timeout = args.timeout
    n_workers = args.n_workers
    n_threads_per_worker = args.n_threads_per_worker

    assert repos_loc.exists()
    run(repos_loc, timeout, n_workers, n_threads_per_worker)
