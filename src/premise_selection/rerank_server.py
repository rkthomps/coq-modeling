from typing import Optional, Any
import argparse
import sys, os
from pathlib import Path

from werkzeug.wrappers import Request, Response
from werkzeug.serving import run_simple

import requests
from jsonrpc import JSONRPCResponseManager, dispatcher

from util.constants import SERVER_LOC
from util.util import get_port_map_loc

import logging

log = logging.getLogger("werkzeug")
log.setLevel(logging.ERROR)

from tactic_gen.lm_example import LmExample
from data_management.dataset_file import Sentence
from premise_selection.rerank_example import RerankExample
from premise_selection.premise_model_wrapper import RerankWrapper
from model_deployment.conf_utils import get_ip, get_free_port

wrapper: Optional[RerankWrapper] = None


@dispatcher.add_method
def get_scores(
    rerank_examples_json: list[Any],
) -> list[float]:
    assert wrapper is not None
    examples = [RerankExample.from_json(e) for e in rerank_examples_json]
    return wrapper.get_scores(examples)


@Request.application
def application(request: requests.models.Response):
    response = JSONRPCResponseManager.handle(request.data, dispatcher)
    return Response(response.json, mimetype="application/json")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("checkpoint_loc", help="Location of select model checkpoint.")
    parser.add_argument("id", type=int, help="Model id (important for evaluation).")
    parser.add_argument("pid", type=int, help="Id of the parent process.")

    args = parser.parse_args(sys.argv[1:])

    wrapper = RerankWrapper.from_checkpoint(args.checkpoint_loc)

    id = args.id
    ip = get_ip()
    port = get_free_port()
    log.warning(f"SERVING AT {ip}; {port}")
    port_map_loc = get_port_map_loc(args.pid)
    assert port_map_loc.exists()

    with port_map_loc.open("a") as fout:
        fout.write(f"{id}\t{ip}\t{port}\n")
    run_simple(ip, port, application)
