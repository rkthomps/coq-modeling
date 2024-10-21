from __future__ import annotations
from typing import Any

import os
import shutil
import yaml
import subprocess
from pathlib import Path
from dataclasses import dataclass
from proof_retrieval.proof_retriever import (
    ProofRetrieverConf,
    proof_retriever_conf_from_yaml,
)
from proof_retrieval.retrieved_proof_db import RetrievedProofDB
from concurrent.futures import ProcessPoolExecutor, Future, as_completed
from data_management.splits import DataSplit, get_all_files, FileInfo

from util.constants import RANGO_LOGGER
from util.slurm import (
    JobOption,
    get_conf_queue_slurm_loc,
    run_local,
    main_get_conf_slurm_conf,
    LocalJobConf,
    SlurmJobConf,
)
from util.file_queue import FileQueue
import subprocess

import logging

_logger = logging.getLogger(RANGO_LOGGER)

WORKER_LOC = Path("src/proof_retrieval/retrieved_proof_db_worker.py")


@dataclass
class ProofDBCreatorConf:
    proof_retriever_conf: ProofRetrieverConf
    save_loc: Path
    data_loc: Path
    sentence_db_loc: Path
    data_split_locs: list[Path]

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> ProofDBCreatorConf:
        return cls(
            proof_retriever_conf_from_yaml(yaml_data["proof_retriever_conf"]),
            Path(yaml_data["save_loc"]),
            Path(yaml_data["data_loc"]),
            Path(yaml_data["sentence_db_loc"]),
            [Path(loc) for loc in yaml_data["data_split_locs"]],
        )

    @classmethod
    def load(cls, path: Path) -> ProofDBCreatorConf:
        with path.open("r") as fin:
            return cls.from_yaml(yaml.safe_load(fin))


def init_and_fill_queue(creator_conf: ProofDBCreatorConf, queue_loc: Path):
    q = FileQueue(queue_loc)
    q.initialize()
    splits = [DataSplit.load(loc) for loc in creator_conf.data_split_locs]
    all_files = get_all_files(splits)
    files_to_add: list[FileInfo] = []
    for f in all_files:
        _logger.debug(f"Checking path: {creator_conf.save_loc / f.dp_name}")
        if not (creator_conf.save_loc / f.dp_name).exists():
            files_to_add.append(f)
    q.put_all(files_to_add)


if __name__ == "__main__":
    job_conf = main_get_conf_slurm_conf()
    assert job_conf.conf_loc.exists()
    conf = ProofDBCreatorConf.load(job_conf.conf_loc)
    if conf.save_loc.exists():
        choice = JobOption.from_user(f"{conf.save_loc} exists")
        match choice:
            case JobOption.CONTINUE:
                pass
            case JobOption.STOP:
                raise FileExistsError(f"{conf.save_loc} already exists.")
    os.makedirs(conf.save_loc, exist_ok=True)
    shutil.copy(job_conf.conf_loc, conf.save_loc / RetrievedProofDB.CONF_NAME)
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
                f"proof-ret-db-{conf.save_loc.name}", commands, slurm_loc
            )
            subprocess.run(["sbatch", str(slurm_loc)])
