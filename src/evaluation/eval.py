from __future__ import annotations
from typing import Any

import os
import yaml
import shutil
import subprocess
from pathlib import Path
from evaluation.eval_utils import EvalConf
from data_management.splits import DataSplit, get_all_files, FileInfo
from model_deployment.prove import get_save_loc

from coqstoq import get_theorem_list
from coqstoq.eval_thms import EvalTheorem

from util.slurm import (
    JobOption,
    get_conf_queue_slurm_loc,
    run_local,
    main_get_conf_slurm_conf,
    LocalJobConf,
    SlurmJobConf,
)
from util.file_queue import FileQueue
from util.constants import RANGO_LOGGER
from util.util import set_rango_logger
import subprocess


import logging

_logger = logging.getLogger(RANGO_LOGGER)

WORKER_LOC = Path("src/evaluation/eval_worker.py")


def fill_queue(
    queue_loc: Path,
    conf: EvalConf,
):
    theorem_list = get_theorem_list(conf.split, conf.coqstoq_loc)
    q = FileQueue[EvalTheorem](queue_loc)
    q.initialize()

    ids = conf.proof_ids if conf.proof_ids is not None else range(len(theorem_list))

    print("Num thms:", len(ids))
    queue_num_thms = 0
    for id in ids:
        save_loc = get_save_loc(conf.save_loc, theorem_list[id])
        if not save_loc.exists():
            q.put(theorem_list[id])
            queue_num_thms += 1
    _logger.info(f"Added {queue_num_thms} theorems to the queue.")


if __name__ == "__main__":
    job_conf = main_get_conf_slurm_conf()
    set_rango_logger(__file__, logging.DEBUG)
    assert job_conf.conf_loc.exists()
    with job_conf.conf_loc.open("r") as fin:
        yaml_conf = yaml.safe_load(fin)
    conf = EvalConf.from_yaml(yaml_conf)
    if conf.save_loc.exists():
        choice = JobOption.from_user(f"{conf.save_loc} exists")
        match choice:
            case JobOption.CONTINUE:
                pass
            case JobOption.STOP:
                raise FileExistsError(f"{conf.save_loc} already exists.")
    os.makedirs(conf.save_loc, exist_ok=True)
    shutil.copy(job_conf.conf_loc, conf.save_loc / "conf.yaml")
    conf_loc, queue_loc, slurm_loc = get_conf_queue_slurm_loc(job_conf.conf_loc)
    fill_queue(queue_loc, conf)

    worker_command = (
        f"python3 {WORKER_LOC} --conf_loc {conf_loc} --queue_loc {queue_loc}"
    )
    match job_conf:
        case LocalJobConf(_, n_workers):
            run_local(worker_command, n_workers)
        case SlurmJobConf(_, slurm_conf):
            commands = [
                f"cp -r {conf.sentence_db_loc} /tmp/{conf.sentence_db_loc.name}",
                f"source unity-module-change-revert",
                f"module load opam/2.1.2",
                f"eval $(opam env)",
                worker_command,
            ]
            slurm_conf.write_script(f"eval-{conf.save_loc.name}", commands, slurm_loc)
            subprocess.run(["sbatch", str(slurm_loc)])
