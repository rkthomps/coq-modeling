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
from subprocess import Popen

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
    QUEUE_LOC,
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


def start_servers_and_update_conf(
    eval_conf: EvalConf, device_list: list[int], eval_conf_loc: str
) -> list[Popen[bytes]]:
    server_commands: list[StartModelCommand] = []
    devices: list[int] = []
    clean_eval_confs: list[TopLevelConf] = []
    next_server_num = 0
    for d in device_list:
        clean_eval_conf, next_server_num, commands = to_client_conf(
            eval_conf, next_server_num
        )
        clean_eval_confs.append(clean_eval_conf)
        server_commands.extend(commands)
        devices.extend([d] * len(commands))

    assert len(devices) == len(server_commands)
    final_eval_conf = merge(clean_eval_confs)
    assert isinstance(final_eval_conf, EvalConf)

    clear_port_map()

    server_procs: list[Popen[bytes]] = []
    for d, c in zip(devices, server_commands):
        next_proc = Popen(
            c.to_list(), env=os.environ | {"CUDA_VISIBLE_DEVICES": f"{d}"}
        )
        server_procs.append(next_proc)

    _logger.info("Waiting for servers...")
    port_map = wait_for_servers(next_server_num)
    _logger.info(f"Got port map {port_map}")
    update_ips(final_eval_conf, port_map)

    _logger.info(f"Eval conf: {final_eval_conf}")
    with open(eval_conf_loc, "wb") as fout:
        pickle.dump(final_eval_conf, fout)
    return server_procs


def start_provers(
    n_workers: int,
    eval_conf_loc: str,
    eval_queue_loc: Path,
) -> list[Popen[bytes]]:
    worker_procs: list[Popen[bytes]] = []
    for _ in range(n_workers):
        worker_cmd = [
            "python3",
            "src/evaluation/eval_worker.py",
            eval_conf_loc,
            eval_queue_loc,
        ]
        worker_proc = Popen(worker_cmd)
        worker_procs.append(worker_proc)
    return worker_procs


def initialize_and_fill_queue(queue_loc: Path, eval_conf: EvalConf):
    proof_map = create_eval_proof_map(eval_conf)
    q = FileQueue[tuple[FileInfo, int]](queue_loc)
    q.initialize()
    if eval_conf.max_eval_proofs is not None:
        q.put_all(proof_map.proofs[: eval_conf.max_eval_proofs])
    else:
        q.put_all(proof_map.proofs)


def run(
    eval_conf: EvalConf,
    n_workers: int,
    device_list: list[int],
):
    time_str = datetime.now().strftime("%m%d%H%M%S")
    eval_conf_loc = CLEAN_CONFIG + "-" + time_str
    eval_queue_loc = Path(QUEUE_LOC + "-" + time_str)
    initialize_and_fill_queue(eval_queue_loc, eval_conf)
    server_proces = start_servers_and_update_conf(eval_conf, device_list, eval_conf_loc)
    prover_procs = start_provers(
        n_workers,
        eval_conf_loc,
        eval_queue_loc,
    )
    for p in prover_procs:
        p.wait()
    for p in server_proces:
        p.kill()


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("conf_loc", help="Location of eval configuration")
    parser.add_argument("n_workers", type=int, help="Number of workers to use.")
    parser.add_argument(
        "device_list", type=int, nargs="+", help="List of gpu devices to use."
    )
    args = parser.parse_args(sys.argv[1:])

    conf_loc = Path(args.conf_loc)
    n_workers = args.n_workers
    device_list = args.device_list

    assert conf_loc.exists()
    assert isinstance(n_workers, int)
    assert isinstance(device_list, list)

    with conf_loc.open("r") as fin:
        conf = yaml.load(fin, Loader=yaml.Loader)

    eval_conf = EvalConf.from_yaml(conf)
    if eval_conf.save_loc.exists():
        raise FileExistsError(f"{eval_conf.save_loc}")
    os.makedirs(eval_conf.save_loc)
    shutil.copy(conf_loc, eval_conf.save_loc / "conf.yaml")

    run(eval_conf, n_workers, device_list)
