from __future__ import annotations
from typing import Optional
import logging
import os
import ipdb
import re
import datetime
from dataclasses import dataclass

from coqpyt.coq.base_file import CoqFile


def get_fresh_path(dirname: str, fresh_base: str) -> str:
    name = fresh_base
    while os.path.exists(os.path.join(dirname, name)):
        name = "_" + name
    return os.path.join(dirname, name)


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
    tmp_path = get_fresh_path(".", "tmp.v")
    try:
        with open(tmp_path, "w") as fout:
            fout.write(proof_text)
        with CoqFile(tmp_path) as coq_file:
            return [s.text for s in coq_file.steps]
    finally:
        os.remove(tmp_path)

@dataclass
class DPStartLog:
    name: str

    def print(self) -> str:
        return f"Starting {self.name}"
    
    @classmethod
    def recover(cls, s: str) -> DPStartLog:
        prefix = "Starting "
        assert s.startswith(prefix)
        return DPStartLog(s[len(prefix):])


@dataclass
class DPLoadLog:
    name: str

    def print(self) -> str:
        return f"Loaded {self.name}"
    
    @classmethod
    def recover(cls, s: str) -> DPLoadLog:
        prefix = "Loaded "
        assert s.startswith(prefix)
        return DPLoadLog(s[len(prefix):])



@dataclass
class DPEndLog:
    name: str

    def print(self) -> str:
        return f"Ending {self.name}"
    
    @classmethod
    def recover(cls, s: str) -> DPEndLog:
        prefix = "Ending "
        assert s.startswith(prefix)
        return DPEndLog(s[len(prefix):])


Log = DPStartLog | DPLoadLog | DPEndLog

def print_info(log: Log, logger: logging.Logger):
    logger.info(log.print())

_log_pattern = re.compile(r"(.*?); (.*?); (.*?); (.*)") 

def parse_log(s: str) -> Optional[tuple[datetime.datetime, Log]]:
    log_match = _log_pattern.match(s)
    if log_match is None:
        return None
    time_str, _, _, msg = log_match.groups()
    time = datetime.datetime.strptime(time_str + "000", r"%Y-%m-%d %H:%M:%S,%f")

    if msg.startswith("Starting "):
        return time, DPStartLog.recover(msg)
    if msg.startswith("Loaded "):
        return time, DPLoadLog.recover(msg)
    if msg.startswith("Ending "):
        return time, DPEndLog.recover(msg)
    return None


def parse_logs(path: str) -> list[tuple[datetime.datetime, Log]]:
    logs: list[tuple[datetime.datetime, Log]] = []
    with open(path, "r") as fin:
        for line in fin.readlines():
            parse_attempt = parse_log(line)
            if parse_attempt:
                time, log = parse_attempt
                logs.append((time, log))
    return logs


def get_num_dps_processed(logs: list[tuple[datetime.datetime, Log]]) -> int:
    num_processed = 0
    for _, l in logs:
        match l:
            case DPEndLog():
                num_processed += 1
            case _:
                continue
    return num_processed


def get_outstanding_dp_ends(logs: list[tuple[datetime.datetime, Log]]) -> list[tuple[str, datetime.datetime]]:
    open_set: dict[str, datetime.datetime] = {} 
    for t, log in logs:
        match log:
            case DPStartLog():
                open_set[log.name] = t
            case DPEndLog():
                assert log.name in open_set
                open_set.pop(log.name)
            case _:
                continue
    return list(open_set.items())


def get_outstanding_dp_loads(logs: list[tuple[datetime.datetime, Log]]) -> list[tuple[str, datetime.datetime]]:
    open_set: dict[str, datetime.datetime] = {} 
    for t, log in logs:
        match log:
            case DPStartLog():
                open_set[log.name] = t
            case DPLoadLog():
                assert log.name in open_set
                open_set.pop(log.name)
            case _:
                continue
    return list(open_set.items())

