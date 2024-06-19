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
    create_eval_proof_map,
    wait_for_servers,
    EvalConf,
)
from data_management.splits import FileInfo

from util.constants import CLEAN_CONFIG
from util.util import get_basic_logger, clear_port_map
from util.file_queue import FileQueue

_logger = get_basic_logger(__name__)

RUN_MODELS_LOC = Path("./jobs/run-models.sh")
TACTIC_SERVER_LOC = Path("./src/model_deployment/tactic_gen_server.py")
GPU_SBATCH_LOC = Path("./jobs/run-gpus.sh")
PROOF_SBATCH_LOC = Path("./jobs/run-proofs.sh")

QUEUE_LOC = "./queue"


def make_executable(p: Path):
    assert p.exists()
    st = os.stat(p)
    os.chmod(p, st.st_mode | stat.S_IEXEC)


def start_servers_and_update_conf(
    eval_conf: EvalConf, timeout: str, n_gpu: int, eval_conf_loc: str
):
    server_commands: Optional[list[StartModelCommand]] = None
    clean_eval_confs: list[TopLevelConf] = []
    next_server_num = 0
    for _ in range(n_gpu):
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
            "#!/bin/bash\n" + "source venv/bin/activate\n" + "\n".join(commands)
        )
        fout.write(run_model_file)
    make_executable(RUN_MODELS_LOC)

    server_sbatch = (
        "#!/bin/bash\n"
        f"#SBATCH -p gpu-preempt\n"
        f"#SBATCH -t {timeout}\n"
        f"#SBATCH --ntasks={n_gpu}\n"
        f"#SBATCH --gres=gpu:{n_gpu}\n"
        f"#SBATCH --mem=16G\n"
        f"#SBATCH -o slurm-serve-%j.out\n"
        f"srun -l --gres=gpu:1 {RUN_MODELS_LOC}\n"
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
    n_workers: int,
    n_threads_per_worker: int,
    eval_conf_loc: str,
    eval_queue_loc: Path,
):
    worker_out_loc = Path("slurm-out")
    os.makedirs(worker_out_loc, exist_ok=True)

    proof_sbatch = (
        "#!/bin/bash\n"
        f"#SBATCH -p cpu-preempt\n"
        f"#SBATCH -c {n_threads_per_worker}\n"
        f"#SBATCH -t {timeout}\n"
        f"#SBATCH --array=0-{n_workers - 1}\n"
        f"#SBATCH --mem=16G\n"
        f"#SBATCH -o {worker_out_loc}/slurm-prove-%j.out\n"
        f"sbcast sentences.db /tmp/sentences.db\n"
        f"source venv/bin/activate\n"
        f"python3 src/evaluation/eval_worker.py {eval_conf_loc} {eval_queue_loc}\n"
    )

    with PROOF_SBATCH_LOC.open("w") as fout:
        fout.write(proof_sbatch)

    # Start proof workers
    subprocess.run(["sbatch", f"{PROOF_SBATCH_LOC}"])


def initialize_and_fill_queue(queue_loc: Path, eval_conf: EvalConf):
    proof_map = create_eval_proof_map(eval_conf)
    q = FileQueue[tuple[FileInfo, int]](queue_loc)
    q.initialize()
    q.put_all(proof_map.proofs)


def run(
    eval_conf: EvalConf,
    timeout: str,
    n_gpu: int,
    n_workers: int,
    n_threads_per_worker: int,
):
    time_str = datetime.now().strftime("%m%d%H%M%S")
    eval_conf_loc = CLEAN_CONFIG + "-" + time_str
    eval_queue_loc = Path(QUEUE_LOC + "-" + time_str)
    initialize_and_fill_queue(eval_queue_loc, eval_conf)
    start_servers_and_update_conf(eval_conf, timeout, n_gpu, eval_conf_loc)
    start_provers(
        eval_conf,
        timeout,
        n_workers,
        n_threads_per_worker,
        eval_conf_loc,
        eval_queue_loc,
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("conf_loc", help="Location of eval configuration")
    parser.add_argument("timeout", help="Timeout for evaluation")
    parser.add_argument("n_gpus", type=int, help="Number of gpus to use.")
    parser.add_argument("n_workers", type=int, help="Number of workers to use.")
    parser.add_argument(
        "n_threads_per_worker", type=int, help="Number of threads per worker."
    )
    args = parser.parse_args(sys.argv[1:])

    conf_loc = Path(args.conf_loc)
    timeout = args.timeout
    n_gpus = args.n_gpus
    n_workers = args.n_workers
    n_threads_per_worker = args.n_threads_per_worker

    assert conf_loc.exists()
    assert isinstance(timeout, str)
    assert isinstance(n_gpus, int)
    assert isinstance(n_workers, int)
    assert isinstance(n_threads_per_worker, int)

    with conf_loc.open("r") as fin:
        conf = yaml.load(fin, Loader=yaml.Loader)

    eval_conf = EvalConf.from_yaml(conf)
    if eval_conf.save_loc.exists():
        raise FileExistsError(f"{eval_conf.save_loc}")
    os.makedirs(eval_conf.save_loc)
    shutil.copy(conf_loc, eval_conf.save_loc / "conf.yaml")

    run(eval_conf, timeout, n_gpus, n_workers, n_threads_per_worker)
