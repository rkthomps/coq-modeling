from __future__ import annotations
from typing import Optional
from typing import Any
import logging
import stat
import json
import os
import re
from pathlib import Path, Path
import datetime
from dataclasses import dataclass

from coqpyt.coq.base_file import CoqFile
from util.constants import PORT_MAP_NAME, TMP_LOC


@dataclass
class StepID:
    file: str
    proof_idx: int
    step_idx: int

    def __hash__(self) -> int:
        return hash((self.file, self.proof_idx, self.step_idx))

    def to_string(self) -> str:
        return json.dumps(self.to_json())

    def to_json(self) -> Any:
        return {
            "file": self.file,
            "proof_idx": self.proof_idx,
            "step_idx": self.step_idx,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> StepID:
        return cls(
            json_data["file"],
            json_data["proof_idx"],
            json_data["step_idx"],
        )

    @classmethod
    def from_string(cls, s: str) -> StepID:
        return cls.from_json(json.loads(s))

    @classmethod
    def from_step_idx(
        cls, step_idx: int, proof_idx: int, dset_file: DatasetFile
    ) -> StepID:
        return StepID(dset_file.dp_name, proof_idx, step_idx)


@dataclass
class FlexibleUrl:
    id: int
    protocol: str
    ip: str
    port: Optional[int]

    def get_url(self) -> str:
        if self.port is None:
            raise ValueError(f"Port has not been assigned for url {id}")
        return f"{self.protocol}://{self.ip}:{self.port}"

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> FlexibleUrl:
        port = None
        if "port" in yaml_data:
            port = yaml_data["port"]
        return cls(yaml_data["id"], yaml_data["protocol"], yaml_data["ip"], port)


def get_port_map_loc(pid: int) -> Path:
    port_map_loc = TMP_LOC / (PORT_MAP_NAME + f"-{pid}")
    return port_map_loc


def clear_port_map():
    port_map_loc = get_port_map_loc(os.getpid())
    os.makedirs(TMP_LOC, exist_ok=True)
    if os.path.exists(port_map_loc):
        os.remove(port_map_loc)
    with port_map_loc.open("w") as _:
        pass


def make_executable(p: Path):
    assert p.exists()
    st = os.stat(p)
    os.chmod(p, st.st_mode | stat.S_IEXEC)


def read_port_map() -> dict[int, tuple[str, int]]:
    port_map_loc = get_port_map_loc(os.getpid())
    port_map: dict[int, tuple[str, int]] = {}
    with port_map_loc.open("r") as fin:
        for line in fin:
            lineitems = line.strip().split("\t")
            assert len(lineitems) == 3
            id = int(lineitems[0])
            ip = lineitems[1]
            port = int(lineitems[2])
            port_map[id] = (ip, port)
    return port_map


def get_flexible_url(id: int, ip_addr: str, port: Optional[int] = None) -> FlexibleUrl:
    return FlexibleUrl(id, "http", ip_addr, port)


def get_fresh_path(dirname: Path, fresh_base: str) -> Path:
    name = fresh_base
    loc = dirname / name
    while loc.exists():
        name = "_" + name
        loc = dirname / name
    return loc


def get_log_level() -> int:
    if "LOG_LEVEL" not in os.environ:
        return logging.WARNING
    match os.environ["LOG_LEVEL"]:
        case "DEBUG":
            return logging.DEBUG
        case "INFO":
            return logging.INFO
        case "WARNING":
            return logging.WARNING
        case "ERROR":
            return logging.ERROR
        case _:
            return logging.WARNING


def get_basic_logger(name: str) -> logging.Logger:
    level = get_log_level()
    logger = logging.Logger(name)
    handler = logging.StreamHandler()
    handler.setLevel(level)
    formatter = logging.Formatter("%(asctime)s; %(name)s; %(levelname)s; %(message)s")
    handler.setFormatter(formatter)
    logger.addHandler(handler)
    logger.propagate = False
    return logger


_logger = get_basic_logger(__name__)


def get_simple_steps(proof_text: str) -> list[str]:
    tmp_path = get_fresh_path(Path("."), "tmp.v")
    try:
        with open(tmp_path, "w") as fout:
            fout.write(proof_text)
        with CoqFile(str(tmp_path.resolve())) as coq_file:
            return [s.text for s in coq_file.steps]
    finally:
        os.remove(tmp_path)


class LogEntry:
    log_pattern = re.compile(r"(.*?); (.*?); (.*?); (.*)")

    def __init__(
        self, time: datetime.datetime, name: str, entry_type: str, message: str
    ) -> None:
        self.time = time
        self.name = name
        self.entry_type = entry_type
        self.message = message

    @classmethod
    def from_line(cls, line: str) -> LogEntry:
        log_match = cls.log_pattern.match(line)
        if log_match is None:
            raise ValueError(f"Could not parse log line {line}")
        time_str, name, entry_type, message = log_match.groups()
        time = datetime.datetime.strptime(time_str + "000", r"%Y-%m-%d %H:%M:%S,%f")
        return cls(time, name, entry_type, message)


def get_log_entries(file: str) -> list[LogEntry]:
    log_entries: list[LogEntry] = []
    with open(file, "r") as fin:
        for line in fin:
            try:
                log_entry = LogEntry.from_line(line.strip())
                log_entries.append(log_entry)
            except ValueError:
                _logger.debug(f"Could not parse line: {line}")
                pass
    return log_entries
