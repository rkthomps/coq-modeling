from __future__ import annotations
from typing import Optional
import os
import ipdb
import re
import datetime
from dataclasses import dataclass

import logging 
logging.basicConfig(level=logging.INFO)

from coqpyt.coq.base_file import CoqFile

LOGGER = logging.getLogger(__name__)


def get_fresh_path(dirname: str, fresh_base: str) -> str:
    name = fresh_base
    while os.path.exists(os.path.join(dirname, name)):
        name = "_" + name
    return os.path.join(dirname, name)


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

_log_pattern = re.compile(r"(.*?):(.*?):(.*)")

def parse_log(s: str) -> Optional[Log]:
    msg_match = _log_pattern.match(s)
    if msg_match is None:
        return None
    _, _, msg = msg_match.groups()

    if msg.startswith("Starting "):
        return DPStartLog.recover(msg)
    if msg.startswith("Loaded "):
        return DPLoadLog.recover(msg)
    if msg.startswith("Ending "):
        return DPEndLog.recover(msg)
    return None


def parse_logs(path: str) -> list[Log]:
    logs: list[Log] = []
    with open(path, "r") as fin:
        for line in fin.readlines():
            parse_attempt = parse_log(line)
            if parse_attempt:
                log = parse_attempt
                logs.append(log)
    return logs


def get_num_dps_processed(logs: list[Log]) -> int:
    num_processed = 0
    for l in logs:
        match l:
            case DPEndLog():
                num_processed += 1
            case _:
                continue
    return num_processed


def get_outstanding_dp_ends(logs: list[Log]) -> list[str]:
    open_set: set[str] = set()
    for log in logs:
        match log:
            case DPStartLog():
                open_set.add(log.name)
            case DPEndLog():
                assert log.name in open_set
                open_set.remove(log.name)
            case _:
                continue
    return list(open_set)


def get_outstanding_dp_loads(logs: list[Log]) -> list[str]:
    open_set: set[str] = set()
    for log in logs:
        match log:
            case DPStartLog():
                open_set.add(log.name)
            case DPLoadLog():
                assert log.name in open_set
                open_set.remove(log.name)
            case _:
                continue
    return list(open_set)

