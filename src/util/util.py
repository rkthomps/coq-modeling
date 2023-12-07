import logging
import os

from coqpyt.coq.base_file import CoqFile


def get_fresh_path(dirname: str, fresh_base: str) -> str:
    name = fresh_base
    while os.path.exists(os.path.join(dirname, name)):
        name = "_" + name
    return os.path.join(dirname, name)


def get_basic_logger(name: str, level: int) -> logging.Logger:
    logger = logging.Logger(name)
    handler = logging.StreamHandler()
    handler.setLevel(level)
    formatter = logging.Formatter("%(asctime)s; %(name)s; %(levelname)s; %(message)s")
    handler.setFormatter(formatter)
    logger.addHandler(handler)
    logger.propagate = False
    return logger


_logger = get_basic_logger(__name__, logging.WARNING)


def get_simple_steps(proof_text: str) -> list[str]:
    tmp_path = get_fresh_path(".", "tmp.v")
    try:
        with open(tmp_path, "w") as fout:
            fout.write(proof_text)
        with CoqFile(tmp_path) as coq_file:
            return [s.text for s in coq_file.steps]
    finally:
        os.remove(tmp_path)
