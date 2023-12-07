import logging
import os

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
