from __future__ import annotations
from typing import Optional
from typing import Any
import logging
import stat
import os
import re
from pathlib import Path, Path
import datetime
from dataclasses import dataclass

from coqpyt.coq.base_file import CoqFile
from util.constants import (
    PORT_MAP_NAME,
    TMP_LOC,
    SRC_LOC,
    SCRIPTS_LOC,
    LOG_LOC,
    RANGO_LOGGER,
)


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


def set_rango_logger(main_path: str, level: int):
    log_p = Path(main_path).resolve()
    if log_p.resolve().is_relative_to(SRC_LOC.resolve()):
        log_dir = LOG_LOC / "src" / log_p.relative_to(SRC_LOC.resolve()).with_suffix("")
    elif log_p.resolve().is_relative_to(SCRIPTS_LOC.resolve()):
        log_dir = (
            LOG_LOC
            / "scripts"
            / log_p.relative_to(SCRIPTS_LOC.resolve()).with_suffix("")
        )
    else:
        raise ValueError(f"Could not find log location for {log_p}")

    os.makedirs(log_dir, exist_ok=True)
    logtime = datetime.datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
    log_loc = log_dir / f"{logtime}.log"

    rango_logger = logging.getLogger(RANGO_LOGGER)
    rango_logger.setLevel(level)
    assert len(rango_logger.handlers) == 0
    rango_logger.handlers.clear()
    fileHandler = logging.FileHandler(log_loc)
    fileHandler.setFormatter(
        logging.Formatter("%(asctime)s; %(levelname)s; %(message)s")
    )
    rango_logger.addHandler(fileHandler)

    streamHandler = logging.StreamHandler()
    streamHandler.setFormatter(logging.Formatter("%(levelname)s; %(message)s"))
    rango_logger.addHandler(streamHandler)
    rango_logger.propagate = False


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


def get_simple_steps(proof_text: str) -> list[str]:
    tmp_path = get_fresh_path(Path("."), "tmp.v")
    try:
        with open(tmp_path, "w") as fout:
            fout.write(proof_text)
        with CoqFile(str(tmp_path.resolve())) as coq_file:
            return [s.text for s in coq_file.steps]
    finally:
        os.remove(tmp_path)
