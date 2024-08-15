from __future__ import annotations
from typing import Optional
import pickle
import sys, os
import shutil
import stat
import subprocess
from typing import Any
from pathlib import Path
from dataclasses import dataclass
from datetime import datetime

import argparse
import yaml
from model_deployment.conf_utils import (
    merge,
    to_client_conf,
    update_ips,
    TopLevelConf,
    StartModelCommand,
)
from evaluation.eval_utils import (
    initialize_and_fill_queue,
    wait_for_servers,
    EvalConf,
)
from data_management.splits import FileInfo

from util.constants import CLEAN_CONFIG, TMP_LOC, QUEUE_NAME
from util.util import get_basic_logger, clear_port_map, make_executable
from util.file_queue import FileQueue

_logger = get_basic_logger(__name__)

TACTIC_SERVER_LOC = Path("./src/model_deployment/tactic_gen_server.py")
RUN_MODELS_LOC = Path("./slurm/jobs/run-models.sh")
GPU_SBATCH_LOC = Path("./slurm/jobs/run-gpus.sh")
PROOF_SBATCH_LOC = Path("./slurm/jobs/run-proofs.sh")


def start_servers_and_update_conf(
    eval_conf: EvalConf,
    timeout: str,
    gpu_partition: str,
    n_gpu_nodes: int,
    n_devices_per_node: int,
    eval_conf_loc: Path,
):
    server_commands: Optional[list[StartModelCommand]] = None
    clean_eval_confs: list[TopLevelConf] = []
    next_server_num = 0
    for _ in range(n_gpu_nodes * n_devices_per_node):
        clean_eval_conf, next_server_num, commands = to_client_conf(
            eval_conf, next_server_num
        )
        clean_eval_confs.append(clean_eval_conf)
        if server_commands is None:
            server_commands = commands
        else:
            assert len(server_commands) == len(commands)
    assert server_commands is not None

    final_eval_conf = merge(clean_eval_confs)
    assert isinstance(final_eval_conf, EvalConf)

    clear_port_map()
    with RUN_MODELS_LOC.open("w") as fout:
        commands = [
            " ".join(c.to_list_slurm("SLURM_PROCID", len(server_commands)))
            for c in server_commands
        ]
        run_model_file = (
            "#!/bin/bash\n" + "source venv/bin/activate\n" + " &\n".join(commands)
        )
        fout.write(run_model_file)
    make_executable(RUN_MODELS_LOC)

    server_sbatch = (
        "#!/bin/bash\n"
        f"#SBATCH -p {gpu_partition}\n"
        f"#SBATCH -t {timeout}\n"
        f"#SBATCH --nodes={n_gpu_nodes}\n"
        f"#SBATCH --ntasks={n_gpu_nodes * n_devices_per_node}\n"
        f"#SBATCH --gpus-per-task=1\n"
        f"#SBATCH --constraint=2080ti\n"
        f"#SBATCH --mem-per-cpu=16G\n"
        f"#SBATCH --no-requeue\n"
        f"#SBATCH --mail-type=BEGIN,END,FAIL\n"
        f"#SBATCH --job-name={eval_conf.start_at}-serve\n"
        f"#SBATCH -o slurm/out/slurm-serve-%j.out\n"
        f"srun -l {RUN_MODELS_LOC}\n"
    )

    with GPU_SBATCH_LOC.open("w") as fout:
        fout.write(server_sbatch)

    # Start gpus
    _logger.info("Starting gpu servers...")
    subprocess.run(["sbatch", f"{GPU_SBATCH_LOC}"])

    _logger.info("Waiting for servers...")
    port_map = wait_for_servers(next_server_num)
    _logger.info(f"Got port map {port_map}")
    update_ips(final_eval_conf, port_map)

    _logger.info(f"Eval conf: {final_eval_conf}")
    with open(eval_conf_loc, "wb") as fout:
        pickle.dump(final_eval_conf, fout)


def start_provers(
    eval_conf: EvalConf,
    timeout: str,
    cpu_partition: str,
    n_workers: int,
    n_threads_per_worker: int,
    eval_conf_loc: Path,
    eval_queue_loc: Path,
    only_new: bool,
):
    if only_new:
        command_str = f"python3 src/evaluation/eval_worker.py {eval_conf_loc} {eval_queue_loc} --only_new"
    else:
        command_str = (
            f"python3 src/evaluation/eval_worker.py {eval_conf_loc} {eval_queue_loc}"
        )
    proof_sbatch = (
        "#!/bin/bash\n"
        f"#SBATCH -p {cpu_partition}\n"
        f"#SBATCH -c {n_threads_per_worker}\n"
        f"#SBATCH -t {timeout}\n"
        f"#SBATCH --array=0-{n_workers - 1}\n"
        f"#SBATCH --mem=16G\n"
        f"#SBATCH --job-name={eval_conf.start_at}-prove\n"
        f"#SBATCH -o slurm/out/slurm-prove-%j.out\n"
        f"sbcast {eval_conf.sentence_db_loc} /tmp/sentences.db\n"
        f"source venv/bin/activate\n"
        f"module load opam/2.1.2\n"
        f"eval $(opam env)\n"
        f"{command_str}\n"
    )

    with PROOF_SBATCH_LOC.open("w") as fout:
        fout.write(proof_sbatch)

    # Start proof workers
    subprocess.run(["sbatch", f"{PROOF_SBATCH_LOC}"])


def run(
    eval_conf: EvalConf,
    timeout: str,
    gpu_partition: str,
    cpu_partition: str,
    n_gpu_nodes: int,
    n_devices_per_node: int,
    n_workers: int,
    n_threads_per_worker: int,
    only_new: bool,
):
    time_str = datetime.now().strftime("%m%d%H%M%S")
    eval_conf_loc = TMP_LOC / (CLEAN_CONFIG + "-" + time_str)
    eval_queue_loc = TMP_LOC / (QUEUE_NAME + "-" + time_str)
    initialize_and_fill_queue(eval_queue_loc, eval_conf)
    start_servers_and_update_conf(
        eval_conf,
        timeout,
        gpu_partition,
        n_gpu_nodes,
        n_devices_per_node,
        eval_conf_loc,
    )
    start_provers(
        eval_conf,
        timeout,
        cpu_partition,
        n_workers,
        n_threads_per_worker,
        eval_conf_loc,
        eval_queue_loc,
        only_new,
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("conf_loc", help="Location of eval configuration")
    parser.add_argument("timeout", help="Timeout for evaluation")
    parser.add_argument("gpu_partition", help="GPU Partition to use.")
    parser.add_argument("cpu_partition", help="CPU Partition to use.")
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
    gpu_partition = args.gpu_partition
    cpu_partition = args.cpu_partition
    n_gpu_nodes = args.n_gpu_nodes
    n_devices_per_node = args.n_devices_per_node
    n_workers = args.n_workers
    n_threads_per_worker = args.n_threads_per_worker

    assert conf_loc.exists()
    assert isinstance(timeout, str)
    assert isinstance(gpu_partition, str)
    assert isinstance(cpu_partition, str)
    assert isinstance(n_gpu_nodes, int)
    assert isinstance(n_devices_per_node, int)
    assert isinstance(n_workers, int)
    assert isinstance(n_threads_per_worker, int)

    with conf_loc.open("r") as fin:
        conf = yaml.load(fin, Loader=yaml.Loader)
    eval_conf = EvalConf.from_yaml(conf)

    only_new = False
    if eval_conf.save_loc.exists():
        answer = input(
            f"{eval_conf.save_loc} already exists. r = Restart; c = Continue; o = Only New; s = Stop; (r/c/o/s?): "
        )
        if answer.lower() == "r":
            shutil.rmtree(eval_conf.save_loc)
        elif answer.lower() == "c":
            pass
        elif answer.lower() == "o":
            only_new = True
        else:
            raise FileExistsError(f"{eval_conf.save_loc}")
    os.makedirs(eval_conf.save_loc, exist_ok=True)
    shutil.copy(conf_loc, eval_conf.save_loc / "conf.yaml")

    run(
        eval_conf,
        timeout,
        gpu_partition,
        cpu_partition,
        n_gpu_nodes,
        n_devices_per_node,
        n_workers,
        n_threads_per_worker,
        only_new,
    )
