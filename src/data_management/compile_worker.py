import sys, os
import argparse
from pathlib import Path
import subprocess

from util.file_queue import FileQueue, EmptyFileQueueError
from util.util import get_basic_logger

_logger = get_basic_logger(__name__)


if __name__ == "__main__":
    parser = argparse.ArgumentParser("Argument parser for compile worker.")
    parser.add_argument("queue_loc")
    parser.add_argument("n_threads", type=int)

    args = parser.parse_args(sys.argv[1:])
    queue_loc = Path(args.queue_loc)
    n_threads = args.n_threads

    top_dir = Path(os.curdir).resolve()
    queue = FileQueue[Path](queue_loc)
    while True:
        os.chdir(top_dir)
        try:
            compile_path = queue.get()
            _logger.info(f"Compiling {compile_path}")
            os.chdir(compile_path)
            _ = subprocess.run(["make", "clean"])
            result = subprocess.run(["make", f"-j{n_threads}"])
        except EmptyFileQueueError:
            break
