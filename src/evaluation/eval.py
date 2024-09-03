from __future__ import annotations
from typing import Any

import os
import yaml
import shutil
import subprocess
from pathlib import Path
from model_deployment.prove import load_summary, errored_summary, get_save_name
from evaluation.eval_utils import EvalConf, create_eval_proof_map
from data_management.splits import DataSplit, get_all_files, FileInfo

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


def get_proofs_to_add(
    save_loc: Path, proofs: list[tuple[FileInfo, int]], rerun_errors: bool
) -> list[tuple[FileInfo, int]]:
    existing_names = set(f.name for f in save_loc.iterdir())
    proofs_to_add: list[tuple[FileInfo, int]] = []
    for f_info, i in proofs:
        save_name = get_save_name(f_info, i)
        if save_name not in existing_names:
            proofs_to_add.append((f_info, i))
        else:
            summary_loc = save_loc / save_name
            existing_summary = load_summary(summary_loc)
            if rerun_errors and errored_summary(existing_summary):
                proofs_to_add.append((f_info, i))
    return proofs_to_add


def fill_queue(queue_loc: Path, eval_conf: EvalConf) -> None:
    q = FileQueue(queue_loc)
    q.initialize()
    proof_map = create_eval_proof_map(
        eval_conf.split,
        eval_conf.data_split_loc,
        eval_conf.sentence_db_loc,
        eval_conf.data_loc,
    )
    start = eval_conf.start_at if eval_conf.start_at is not None else 0
    end = eval_conf.end_at if eval_conf.end_at is not None else len(proof_map)
    proofs = proof_map.proofs[start:end]
    proofs_to_add = get_proofs_to_add(
        eval_conf.save_loc, proofs, eval_conf.rerun_errors
    )
    _logger.info(f"Adding {len(proofs_to_add)} proofs to queue")
    q.put_all(proofs_to_add)


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
                worker_command,
            ]
            slurm_conf.write_script(f"eval-{conf.save_loc.name}", commands, slurm_loc)
            subprocess.run(["sbatch", str(slurm_loc)])
