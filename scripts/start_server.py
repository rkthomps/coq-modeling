from typing import Any
import sys, os
import argparse
from subprocess import Popen

import yaml

from util.constants import DATA_CONF_NAME
from model_deployment.tactic_gen_client import TacticGenClient

CHECKPOINT_LOC = (
    "/home/ubuntu/coq-modeling/models/t5-fid-base-basic-final/checkpoint-110500"
)

MODEL_CONF = {
    "alias": "fid-local",
    "checkpoint_loc": "/home/ubuntu/coq-modeling/models/t5-fid-base-basic-final/checkpoint-110500",
}


def get_lm_config(checkpoint_loc: str) -> Any:
    model_loc = os.path.dirname(checkpoint_loc)
    conf_loc = os.path.join(model_loc, DATA_CONF_NAME)
    with open(conf_loc, "r") as fin:
        conf = yaml.load(fin, Loader=yaml.Loader)
    formatter_conf = conf["lm_formatter"]
    return formatter_conf


def overwrite_lm_config(conf: Any) -> Any:
    ## TO DO - premise model wrapper to start premise server
    return conf


def get_tactic_gen_client(conf: Any, devices: list[int]) -> TacticGenClient:
    for d in devices:
        Popen([f"CUDA_VISIBLE_DEVICES=d", "python3", "src/model_deployment/tactic_gen_server.py"])



# Each client can know about n servers.
# def overwrite_


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
