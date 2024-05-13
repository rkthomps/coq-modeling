from typing import Optional, Any
import argparse
import sys, os
from pathlib import Path

from werkzeug.wrappers import Request, Response
from werkzeug.serving import run_simple

import requests
from jsonrpc import JSONRPCResponseManager, dispatcher

from util.constants import SERVER_LOC, PORT_MAP_LOC

import logging

log = logging.getLogger("werkzeug")
log.setLevel(logging.ERROR)

from tactic_gen.lm_example import LmExample
from data_management.dataset_file import Sentence
from model_deployment.premise_model_wrapper import RerankWrapper
from model_deployment.conf_utils import get_ip

wrapper: Optional[RerankWrapper] = None


@dispatcher.add_method
def get_scores(
    context: str,
    premise_strs: list[str],
) -> list[float]:
    assert wrapper is not None
    return wrapper.get_premise_scores(context, premise_strs)


@Request.application
def application(request: requests.models.Response):
    response = JSONRPCResponseManager.handle(request.data, dispatcher)
    return Response(response.json, mimetype="application/json")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("checkpoint_loc", help="Location of select model checkpoint.")
    parser.add_argument(
        "port", type=int, help="Port on which to run the select server."
    )

    args = parser.parse_args(sys.argv[1:])

    port = args.port
    ip = get_ip()
    port_map_loc = Path(PORT_MAP_LOC)
    assert port_map_loc.exists()

    with port_map_loc.open("a") as fout:
        fout.write(f"{port}\t{ip}\n")

    wrapper = RerankWrapper.from_checkpoint(args.checkpoint_loc)
    serve_path = (Path(f"./{SERVER_LOC}") / str(args.port)).resolve()
    run_simple(get_ip(), args.port, application)
