from __future__ import annotations
from typing import Any, Optional
import argparse
import os
import shutil
import sys
import yaml
from enum import Enum
from datetime import datetime

from dataclasses import dataclass

from pathlib import Path

from util.constants import CLEAN_CONFIG, QUEUE_NAME, SLURM_NAME, TMP_LOC
import subprocess


@dataclass
class SlurmArrayConf:
    partition: str
    num_workers: int
    time_limit: str
    mem_per_node: str
    slurm_out_loc: Path
    cpus_per_worker: int
    gpus_per_worker: int
    machine_constraint: Optional[str]

    ALIAS = "array"

    def write_script(self, job_name: str, commands: list[str], script_loc: Path):
        script = (
            f"#!/bin/bash\n"
            f"#SBATCH --partition={self.partition}\n"
            f"#SBATCH --array=0-{self.num_workers - 1}\n"
            f"#SBATCH --time={self.time_limit}\n"
            f"#SBATCH --mem={self.mem_per_node}\n"
            f"#SBATCH --output={self.slurm_out_loc}/{job_name}-%j.out\n"
            f"#SBATCH --job-name={job_name}\n"
            f"#SBATCH --error={self.slurm_out_loc}/{job_name}-%j.err\n"
            f"#SBATCH --cpus-per-task={self.cpus_per_worker}\n"
            f"#SBATCH --gres=gpu:{self.gpus_per_worker}\n"
        )
        if self.machine_constraint is not None:
            script += f"#SBATCH --constraint={self.machine_constraint}\n"

        script += "\n".join(commands) + "\n"
        with script_loc.open("w") as fout:
            fout.write(script)

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> SlurmArrayConf:
        machine_constraint = None
        if "machine_constraint" in yaml_data:
            machine_constraint = yaml_data["machine_constraint"]

        return cls(
            yaml_data["partition"],
            yaml_data["num_workers"],
            yaml_data["time_limit"],
            yaml_data["mem_per_node"],
            Path(yaml_data["slurm_out_loc"]),
            yaml_data["cpus_per_worker"],
            yaml_data["gpus_per_worker"],
            machine_constraint,
        )

    @classmethod
    def load(cls, path: Path) -> SlurmArrayConf:
        with path.open("r") as fin:
            return cls.from_yaml(yaml.safe_load(fin))


def get_conf_queue_slurm_loc(orig_conf_loc: Path) -> tuple[Path, Path, Path]:
    time_str = datetime.now().strftime("%m%d%H%M%S")
    conf_loc = TMP_LOC / (CLEAN_CONFIG + "-" + time_str)
    queue_loc = TMP_LOC / (QUEUE_NAME + "-" + time_str)
    slurm_loc = TMP_LOC / (SLURM_NAME + "-" + time_str)
    shutil.copy(orig_conf_loc, conf_loc)
    return conf_loc, queue_loc, slurm_loc


SlurmConf = SlurmArrayConf


def slurm_conf_from_yaml(yaml_data: Any) -> SlurmConf:
    attempted_alias = yaml_data["alias"]
    match attempted_alias:
        case SlurmArrayConf.ALIAS:
            return SlurmArrayConf.from_yaml(yaml_data)
        case _:
            raise ValueError(f"Unknown alias {attempted_alias}.")


def run_local(command: str, n_workers: int):
    open_procs: list[subprocess.Popen[bytes]] = []
    for _ in range(n_workers):
        p = subprocess.Popen(
            command, shell=True, stdout=sys.stdout, stderr=sys.stderr, env=os.environ
        )
        open_procs.append(p)
    for p in open_procs:
        p.wait()


def worker_get_conf_queue() -> tuple[Path, Path]:
    parser = argparse.ArgumentParser()
    parser.add_argument("--conf_loc", type=str, required=True)
    parser.add_argument("--queue_loc", type=str, required=True)
    args = parser.parse_args()
    conf_loc = Path(args.conf_loc)
    queue_loc = Path(args.queue_loc)
    assert conf_loc.exists()
    assert queue_loc.exists()
    return conf_loc, queue_loc


@dataclass
class SlurmJobConf:
    conf_loc: Path
    slurm_conf: SlurmConf


@dataclass
class LocalJobConf:
    conf_loc: Path
    n_processes: int


JobConf = SlurmJobConf | LocalJobConf


def main_get_conf_slurm_conf() -> JobConf:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--conf_loc",
        type=str,
        required=True,
        help="Path of the job config.",
    )
    parser.add_argument("--slurm_conf", type=str, help="Path to slurm config.")
    parser.add_argument(
        "--n_workers", type=int, help="Number of workers to use for local processing."
    )
    args = parser.parse_args()
    if not ((args.slurm_conf is not None) ^ (args.n_workers is not None)):
        raise ValueError("Exactly one of slurm_conf and n_workers must be provided.")

    conf_loc = Path(args.conf_loc)
    assert conf_loc.exists()

    if args.slurm_conf is None:
        opt_slurm_conf = None
        assert args.n_workers is not None
        opt_n_workers = args.n_workers
        assert 0 < opt_n_workers
        return LocalJobConf(conf_loc, opt_n_workers)
    else:
        opt_slurm_conf = Path(args.slurm_conf)
        assert opt_slurm_conf.exists()
        opt_n_workers = None
        with opt_slurm_conf.open("r") as fin:
            slurm_conf = slurm_conf_from_yaml(yaml.safe_load(fin))
        return SlurmJobConf(conf_loc, slurm_conf)


class JobOption(Enum):
    CONTINUE = 0
    STOP = 1

    @classmethod
    def from_user(cls, message: str) -> JobOption:
        response = input(f"{message}. Continue or stop? (c/s): ")
        match response:
            case "c":
                return cls.CONTINUE
            case "s":
                return cls.STOP
            case _:
                return cls.STOP
