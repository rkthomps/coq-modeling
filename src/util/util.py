from __future__ import annotations
from typing import Any
import logging
import os
import re
from pathlib import Path, Path
import datetime
from dataclasses import dataclass

from coqpyt.coq.base_file import CoqFile


@dataclass
class FlexibleUrl:
    protocol: str
    ip: str
    port: int

    def get_url(self) -> str:
        return f"{self.protocol}://{self.ip}:{self.port}"

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> FlexibleUrl:
        assert isinstance(yaml_data, str)
        url_pattern = r"(.*?)://(.*?):(.*)"
        url_match = re.match(url_pattern, yaml_data)
        assert url_match is not None
        protocol, ip, port = url_match.groups()
        return cls(protocol, ip, int(port))


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
    tmp_path = get_fresh_path(".", "tmp.v")
    try:
        with open(tmp_path, "w") as fout:
            fout.write(proof_text)
        with CoqFile(tmp_path) as coq_file:
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
