import sys, os
import argparse
import yaml
import shutil
import subprocess
from pathlib import Path
from datetime import datetime

from data_management.splits import DataSplit, Split, FileInfo, get_all_files
from data_management.dataset_utils import DatasetConf, data_conf_from_yaml
from util.constants import TMP_LOC, QUEUE_NAME
from util.file_queue import FileQueue


WORKER_SBATCH_LOC = Path("./slurm/jobs/data-worker.sh")


def fill_queue(queue_loc: Path, data_conf: DatasetConf) -> None:
    q = FileQueue[FileInfo](queue_loc)
    q.initialize()
    data_splits = [DataSplit.load(loc) for loc in data_conf.data_split_locs]
    all_files = get_all_files(data_splits)
    q.put_all(all_files)


def start_workers(
    data_conf: DatasetConf,
    timeout: str,
    n_gpu_nodes: int,
    n_devices_per_node: int,
    n_workers: int,
    n_threads_per_worker: int,
    conf_loc: Path,
    queue_loc: Path,
):
    total_n_gpus = n_gpu_nodes * n_devices_per_node
    if 0 < total_n_gpus:
        print(f"There will be {total_n_gpus} given the nonzero number of gpus.")
        raise ValueError("NEED TO HANDLE GPU CASE")
        proof_sbatch = (
            "#!/bin/bash\n"
            f"#SBATCH -p cpu-preempt\n"
            f"#SBATCH -G {n_threads_per_worker}\n"
            f"#SBATCH -t {timeout}\n"
            f"#SBATCH --array=0-{n_workers - 1}\n"
            f"#SBATCH --mem=16G\n"
            f"#SBATCH -o slurm/out/slurm-prove-%j.out\n"
            f"sbcast {data_conf.sentence_db_loc} /tmp/sentences.db\n"
            f"source venv/bin/activate\n"
            f"python3 src/evaluation/eval_worker.py {conf_loc} {queue_loc}\n"
        )
    else:
        worker_sbatch = (
            "#!/bin/bash\n"
            f"#SBATCH -p cpu\n"
            f"#SBATCH -c {n_threads_per_worker}\n"
            f"#SBATCH -t {timeout}\n"
            f"#SBATCH --array=0-{n_workers - 1}\n"
            f"#SBATCH --mem=16G\n"
            f"#SBATCH -o slurm/out/slurm-{data_conf.output_dataset_loc.name}-%j.out\n"
            f"#SBATCH --job-name={data_conf.output_dataset_loc.name}\n"
            f"sbcast {data_conf.sentence_db_loc} /tmp/sentences.db\n"
            f"source venv/bin/activate\n"
            f"python3 src/data_management/dataset_worker.py {conf_loc} {queue_loc}\n"
        )

    with WORKER_SBATCH_LOC.open("w") as fout:
        fout.write(worker_sbatch)

    # Start proof workers
    subprocess.run(["sbatch", f"{WORKER_SBATCH_LOC}"])


def run(
    data_conf: DatasetConf,
    conf_loc: Path,
    timeout: str,
    n_gpu_nodes: int,
    n_devices_per_node: int,
    n_workers: int,
    n_threads_per_worker: int,
):
    time_str = datetime.now().strftime("%m%d%H%M%S")
    queue_loc = TMP_LOC / (QUEUE_NAME + "-" + time_str)
    new_conf_loc = TMP_LOC / (conf_loc.name + "-" + time_str)
    shutil.copy(conf_loc, new_conf_loc)
    fill_queue(queue_loc, data_conf)
    start_workers(
        data_conf,
        timeout,
        n_gpu_nodes,
        n_devices_per_node,
        n_workers,
        n_threads_per_worker,
        new_conf_loc,
        queue_loc,
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("conf_loc", help="Location of dataset configuration")
    parser.add_argument("timeout", help="Timeout for evaluation")
    parser.add_argument("n_gpu_nodes", type=int, help="Number of gpus nodes to use.")
    parser.add_argument(
        "n_devices_per_node",
        type=int,
        help="Number of devices required on each gpu node.",
    )
    parser.add_argument("n_workers", type=int, help="Number of workers to use.")
    parser.add_argument(
        "n_threads_per_worker", type=int, help="Number of threads per worker."
    )
    args = parser.parse_args(sys.argv[1:])
    os.makedirs(TMP_LOC, exist_ok=True)

    conf_loc = Path(args.conf_loc)
    timeout = args.timeout
    n_gpu_nodes = args.n_gpu_nodes
    n_devices_per_node = args.n_devices_per_node
    n_workers = args.n_workers
    n_threads_per_worker = args.n_threads_per_worker

    assert conf_loc.exists()
    assert isinstance(timeout, str)
    assert isinstance(n_gpu_nodes, int)
    assert isinstance(n_devices_per_node, int)
    assert isinstance(n_workers, int)
    assert isinstance(n_threads_per_worker, int)

    with conf_loc.open("r") as fin:
        conf = yaml.load(fin, Loader=yaml.Loader)
    data_conf = data_conf_from_yaml(conf)
    if data_conf.output_dataset_loc.exists():
        answer = input(
            f"{data_conf.output_dataset_loc} already exists. Overwrite? y/n: "
        )
        if answer.lower() != "y":
            raise FileExistsError(f"{data_conf.output_dataset_loc}")
        shutil.rmtree(data_conf.output_dataset_loc)
    os.makedirs(data_conf.output_dataset_loc)
    shutil.copy(conf_loc, data_conf.output_dataset_loc / "conf.yaml")

    run(
        data_conf,
        conf_loc,
        timeout,
        n_gpu_nodes,
        n_devices_per_node,
        n_workers,
        n_threads_per_worker,
    )
