import sys, os
import argparse
import yaml
import shutil
import subprocess
from pathlib import Path
from datetime import datetime

from data_management.splits import DataSplit, Split
from model_deployment.premise_client import SelectModelConf
from evaluation.eval_utils import PremiseEvalConf, initialize_and_fill_queue
from util.constants import TMP_LOC, QUEUE_NAME
from util.file_queue import FileQueue
from util.util import make_executable


WORKER_SBATCH_LOC = Path("./slurm/jobs/premise-eval-worker.sh")
TASK_FILE_LOC = Path("./slurm/jobs/premise-eval-task.sh")


def start_workers(
    premise_eval_conf: PremiseEvalConf,
    timeout: str,
    n_gpu_nodes: int,
    n_devices_per_node: int,
    n_workers: int,
    n_threads_per_worker: int,
    conf_loc: Path,
    queue_loc: Path,
):
    vec_str = ""
    if isinstance(premise_eval_conf.premise_conf, SelectModelConf):
        if premise_eval_conf.premise_conf.vector_db_loc is not None:
            vec_str = f"cp -r {premise_eval_conf.premise_conf.vector_db_loc} /tmp/{premise_eval_conf.premise_conf.vector_db_loc.name}\n"

    total_n_gpus = n_gpu_nodes * n_devices_per_node
    if 0 < total_n_gpus:
        with TASK_FILE_LOC.open("w") as fout:
            fout.write(
                f"#!/bin/bash\n"
                f"{vec_str}"
                f"source venv/bin/activate\n"
                f"LOG_LEVEL=DEBUG python3 src/evaluation/premise_eval_worker.py {conf_loc} {queue_loc}\n"
            )
        make_executable(TASK_FILE_LOC)
        print(f"There will be {total_n_gpus} given the nonzero number of gpus.")
        worker_sbatch = (
            "#!/bin/bash\n"
            f"#SBATCH -p gpu-preempt\n"
            f"#SBATCH -t {timeout}\n"
            f"#SBATCH --nodes={n_gpu_nodes}\n"
            f"#SBATCH --ntasks={n_gpu_nodes * n_devices_per_node}\n"
            f"#SBATCH --gpus-per-task=1\n"
            f"#SBATCH --constraint=2080ti\n"
            f"#SBATCH --mem-per-cpu=16G\n"
            f"#SBATCH -o slurm/out/slurm-{premise_eval_conf.save_loc.name}-%j.out\n"
            f"sbcast {premise_eval_conf.sentence_db_loc} /tmp/sentences.db\n"
            f"srun -l {TASK_FILE_LOC}\n"
        )
    else:
        worker_sbatch = (
            "#!/bin/bash\n"
            f"#SBATCH -p cpu\n"
            f"#SBATCH -c {n_threads_per_worker}\n"
            f"#SBATCH -t {timeout}\n"
            f"#SBATCH --array=0-{n_workers - 1}\n"
            f"#SBATCH --mem=16G\n"
            f"#SBATCH -o slurm/out/slurm-{premise_eval_conf.save_loc.name}-%j.out\n"
            f"#SBATCH --job-name={premise_eval_conf.save_loc.name}\n"
            f"sbcast {premise_eval_conf.sentence_db_loc} /tmp/sentences.db\n"
            f"source venv/bin/activate\n"
            f"LOG_LEVEL=DEBUG python3 src/evaluation/premise_eval_worker.py {conf_loc} {queue_loc}\n"
        )

    with WORKER_SBATCH_LOC.open("w") as fout:
        fout.write(worker_sbatch)

    # Start proof workers
    subprocess.run(["sbatch", f"{WORKER_SBATCH_LOC}"])


def run(
    premise_eval_conf: PremiseEvalConf,
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
    initialize_and_fill_queue(queue_loc, premise_eval_conf)
    start_workers(
        premise_eval_conf,
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
    parser.add_argument("--conf_loc", help="Location of dataset configuration")
    parser.add_argument("--timeout", help="Timeout for evaluation")
    parser.add_argument("--n_gpu_nodes", type=int, help="Number of gpus nodes to use.")
    parser.add_argument(
        "--n_devices_per_node",
        type=int,
        help="Number of devices required on each gpu node.",
    )
    parser.add_argument("--n_workers", type=int, help="Number of workers to use.")
    parser.add_argument(
        "--n_threads_per_worker", type=int, help="Number of threads per worker."
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
    premise_eval_conf = PremiseEvalConf.from_yaml(conf)
    if premise_eval_conf.save_loc.exists():
        answer = input(f"{premise_eval_conf.save_loc} already exists. Overwrite? y/n: ")
        if answer.lower() != "y":
            raise FileExistsError(f"{premise_eval_conf.save_loc}")
        shutil.rmtree(premise_eval_conf.save_loc)
    os.makedirs(premise_eval_conf.save_loc)
    shutil.copy(conf_loc, premise_eval_conf.save_loc / "conf.yaml")

    run(
        premise_eval_conf,
        conf_loc,
        timeout,
        n_gpu_nodes,
        n_devices_per_node,
        n_workers,
        n_threads_per_worker,
    )
