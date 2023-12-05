import logging


def get_basic_logger(name: str, level: int) -> logging.Logger:
    logger = logging.Logger(name)
    handler = logging.StreamHandler()
    handler.setLevel(level)
    formatter = logging.Formatter("%(asctime)s; %(name)s; %(levelname)s; %(message)s")
    handler.setFormatter(formatter)
    logger.addHandler(handler)
    logger.propagate = False
    return logger
