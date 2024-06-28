from typing import Any
import sys, os
import shutil
import argparse
from pathlib import Path
import yaml

from util.util import get_basic_logger
from util.constants import TMP_LOC

_logger = get_basic_logger(__name__)


def move_data_tar(train_conf: Any) -> None:
    data_loc = Path(train_conf["data_path"])
    data_loc_zipped = Path(str(data_loc) + ".tar.gz")
    if not data_loc_zipped.exists():
        _logger.info(f"Zipped data not found at {data_loc_zipped}. Zipping now.")
        os.system(f"tar -czvf {data_loc_zipped} {data_loc}")
    tmp_loc = Path("/tmp")
    _logger.info(f"Moving data to tmp.")
    shutil.copy(data_loc_zipped, tmp_loc)
    target_loc = tmp_loc / data_loc_zipped.name
    _logger.info(f"Unzipping data to /tmp")
    os.system(f"tar -xzvf {target_loc} -C /tmp")


def move_data(train_conf: Any) -> None:
    data_loc = Path(train_conf["data_path"])
    target_loc = Path("/tmp") / data_loc.name
    if target_loc.exists():
        _logger.info(f"Found previously existing {target_loc}. Using it.")
        return
    shutil.copytree(data_loc, target_loc)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("train_conf_loc")
    args = parser.parse_args(sys.argv[1:])
    train_conf_loc = Path(args.train_conf_loc)

    with train_conf_loc.open("r") as fin:
        conf = yaml.load(fin, Loader=yaml.Loader)
    move_data(conf)
