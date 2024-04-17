from typing import Any
import sys, os
import argparse
from werkzeug.wrappers import Request, Response
from werkzeug.serving import run_simple

import logging

log = logging.getLogger("werkzeug")
log.setLevel(logging.ERROR)

import requests
from jsonrpc import JSONRPCResponseManager, dispatcher

from tactic_gen.lm_example import LmExample
from model_deployment.model_wrapper import ModelWrapper, StubWrapper, wrapper_from_conf
from model_deployment.model_result import ModelResult

wrapper: ModelWrapper = StubWrapper()


@dispatcher.add_method
def get_recs(example_json: Any, n: int, current_proof: str) -> ModelResult:
    example = LmExample.from_json(example_json)
    return wrapper.get_recs(example, n, current_proof).to_json()


@Request.application
def application(request: requests.models.Response):
    response = JSONRPCResponseManager.handle(request.data, dispatcher)
    return Response(response.json, mimetype="application/json")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("alias", help="Alias of the model wrapper")
    parser.add_argument("checkpoint_loc", help="Checkpoint of the model wrapper")
    parser.add_argument("port", type=int, help="Port at which to host the model.")
    args = parser.parse_args(sys.argv[1:])
    conf = {
        "alias": args.alias,
        "checkpoint_loc": args.checkpoint_loc,
    }
    wrapper = wrapper_from_conf(conf)
    print("serving model at checkpoint ", args.checkpoint_loc)
    run_simple("localhost", args.port, application)
