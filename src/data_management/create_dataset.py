from __future__ import annotations
from typing import Any

import os
import yaml
import shutil
import subprocess
from pathlib import Path
from data_management.dataset_utils import DatasetConf, data_conf_from_yaml
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
from util.util import set_rango_logger
import subprocess

import logging

WORKER_LOC = Path("src/data_management/dataset_worker.py")


def fill_queue(queue_loc: Path, data_conf: DatasetConf) -> None:
    q: FileQueue[FileInfo] = FileQueue(queue_loc)
    q.initialize()
    data_splits = [DataSplit.load(loc) for loc in data_conf.data_split_locs]
    add_files: list[FileInfo] = []
    for f in get_all_files(data_splits):
        if not (data_conf.output_dataset_loc / f.dp_name).exists():
            add_files.append(f)
    q.put_all(add_files)


if __name__ == "__main__":
    job_conf = main_get_conf_slurm_conf()
    set_rango_logger(__file__, logging.DEBUG)
    assert job_conf.conf_loc.exists()
    with job_conf.conf_loc.open("r") as fin:
        yaml_conf = yaml.safe_load(fin)
    conf = data_conf_from_yaml(yaml_conf)
    if conf.output_dataset_loc.exists():
        choice = JobOption.from_user(f"{conf.output_dataset_loc} exists")
        match choice:
            case JobOption.CONTINUE:
                pass
            case JobOption.STOP:
                raise FileExistsError(f"{conf.output_dataset_loc} already exists.")
    os.makedirs(conf.output_dataset_loc, exist_ok=True)
    shutil.copy(job_conf.conf_loc, conf.output_dataset_loc / "conf.yaml")
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
            slurm_conf.write_script(
                f"data-{conf.output_dataset_loc.name}", commands, slurm_loc
            )
            subprocess.run(["sbatch", str(slurm_loc)])
