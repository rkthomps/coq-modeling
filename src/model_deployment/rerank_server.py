from typing import Optional, Any
import argparse
import sys, os

from werkzeug.wrappers import Request, Response
from werkzeug.serving import run_simple

import requests
from jsonrpc import JSONRPCResponseManager, dispatcher

import logging

log = logging.getLogger("werkzeug")
log.setLevel(logging.ERROR)

from tactic_gen.lm_example import LmExample
from data_management.dataset_file import Sentence
from model_deployment.premise_model_wrapper import RerankWrapper

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
    wrapper = RerankWrapper.from_checkpoint(args.checkpoint_loc)
    run_simple("localhost", args.port, application)
