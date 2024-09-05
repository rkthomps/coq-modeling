from __future__ import annotations
from typing import Any

import os
import shutil
import yaml
import subprocess
from pathlib import Path
from dataclasses import dataclass
from premise_selection.rerank_client import (
    PremiseClient,
    PremiseConf,
    premise_conf_from_yaml,
)
from premise_selection.retrieved_premise_db import RetrievedPremiseDB
from concurrent.futures import ProcessPoolExecutor, Future, as_completed
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

WORKER_LOC = Path("src/premise_selection/retrieved_premise_db_worker.py")


@dataclass
class PremiseDBCreatorConf:
    premise_conf: PremiseConf
    max_num_premises: int
    save_loc: Path
    data_loc: Path
    sentence_db_loc: Path
    data_split_locs: list[Path]

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> PremiseDBCreatorConf:
        return cls(
            premise_conf_from_yaml(yaml_data["premise_conf"]),
            yaml_data["max_num_premises"],
            Path(yaml_data["save_loc"]),
            Path(yaml_data["data_loc"]),
            Path(yaml_data["sentence_db_loc"]),
            [Path(loc) for loc in yaml_data["data_split_locs"]],
        )

    @classmethod
    def load(cls, path: Path) -> PremiseDBCreatorConf:
        with path.open("r") as fin:
            return cls.from_yaml(yaml.safe_load(fin))


def init_and_fill_queue(creator_conf: PremiseDBCreatorConf, queue_loc: Path):
    q = FileQueue(queue_loc)
    q.initialize()
    splits = [DataSplit.load(loc) for loc in creator_conf.data_split_locs]
    all_files = get_all_files(splits)
    add_files: list[FileInfo] = []
    for f in all_files:
        if not ((creator_conf.save_loc / f.dp_name).exists()):
            add_files.append(f)
    _logger.info(f"Adding {len(add_files)}/{len(all_files)} files to queue")
    q.put_all(add_files)


if __name__ == "__main__":
    job_conf = main_get_conf_slurm_conf()
    set_rango_logger(__file__, logging.DEBUG)
    assert job_conf.conf_loc.exists()
    conf = PremiseDBCreatorConf.load(job_conf.conf_loc)
    if conf.save_loc.exists():
        choice = JobOption.from_user(f"{conf.save_loc} exists")
        match choice:
            case JobOption.CONTINUE:
                pass
            case JobOption.STOP:
                raise FileExistsError(f"{conf.save_loc} already exists.")
    os.makedirs(conf.save_loc, exist_ok=True)
    shutil.copy(job_conf.conf_loc, conf.save_loc / RetrievedPremiseDB.CONF_NAME)
    conf_loc, queue_loc, slurm_loc = get_conf_queue_slurm_loc(job_conf.conf_loc)
    init_and_fill_queue(conf, queue_loc)

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
                f"premise-ret-db-{conf.save_loc.name}", commands, slurm_loc
            )
            subprocess.run(["sbatch", str(slurm_loc)])
