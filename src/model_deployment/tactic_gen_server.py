from typing import Any
import sys, os
import time
import argparse
from pathlib import Path
from werkzeug.wrappers import Request, Response

from werkzeug.serving import run_simple
from util.util import get_basic_logger, get_port_map_loc

import logging

_logger = get_basic_logger(__name__)

log = logging.getLogger("werkzeug")
log.setLevel(logging.DEBUG)

import requests
from jsonrpc import JSONRPCResponseManager, dispatcher

from tactic_gen.lm_example import LmExample
from model_deployment.model_wrapper import ModelWrapper, StubWrapper, wrapper_from_conf
from model_deployment.model_result import ModelResult

from model_deployment.conf_utils import get_ip, get_free_port

wrapper: ModelWrapper = StubWrapper()


@dispatcher.add_method
def get_recs(example_json: Any, n: int, current_proof: str, beam: bool) -> ModelResult:
    example = LmExample.from_json(example_json)
    start = time.time()
    result = wrapper.get_recs(example, n, current_proof, beam).to_json()
    end = time.time()
    return result


@Request.application
def application(request: requests.models.Response):
    response = JSONRPCResponseManager.handle(request.data, dispatcher)
    return Response(response.json, mimetype="application/json")


if __name__ == "__main__":
    # from waitress import serve

    parser = argparse.ArgumentParser()
    parser.add_argument("alias", help="Alias of the model wrapper")
    parser.add_argument("checkpoint_loc", help="Checkpoint of the model wrapper")
    parser.add_argument("id", type=int, help="Id of model.")
    parser.add_argument("pid", type=int, help="Id of the parent process.")
    args = parser.parse_args(sys.argv[1:])

    conf = {
        "alias": args.alias,
        "checkpoint_loc": args.checkpoint_loc,
    }
    log.info("loading model")
    wrapper = wrapper_from_conf(conf)

    id = args.id
    ip = get_ip()
    port = get_free_port()
    log.warning(f"SERVING AT {ip}; {port}")
    port_map_loc = get_port_map_loc(args.pid)
    assert port_map_loc.exists()

    with port_map_loc.open("a") as fout:
        fout.write(f"{id}\t{ip}\t{port}\n")

    run_simple(ip, port, application)
