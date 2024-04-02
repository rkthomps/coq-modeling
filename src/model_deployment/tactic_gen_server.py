from typing import Any
import sys, os
import argparse
from werkzeug.wrappers import Request, Response
from werkzeug.serving import run_simple

import requests
from jsonrpc import JSONRPCResponseManager, dispatcher

from tactic_gen.lm_example import LmExample
from model_deployment.model_wrapper import ModelWrapper, StubWrapper
from model_deployment.model_result import ModelResult

wrapper: ModelWrapper = StubWrapper()


@dispatcher.add_method
def get_recs(example_json: Any, n: int) -> ModelResult:
    example = LmExample.from_json(example_json)
    return wrapper.get_recs(example, n).to_json()


@Request.application
def application(request: requests.models.Response):
    response = JSONRPCResponseManager.handle(request.data, dispatcher)
    return Response(response.json, mimetype="application/json")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("alias", help="Alias of the model wrapper")
    parser.add_argument("checkpoint_loc", help="Checkpoint of the model wrapper")
    parser.add_argument("port", help="Port at which to host the model.")
    args = parser.parse_args(sys.argv[1:])
    run_simple("localhost", 4000, application)
