from typing import Optional, Any
import argparse
from werkzeug.wrappers import Request, Response
from werkzeug.serving import run_simple

import requests
from jsonrpc import JSONRPCResponseManager, dispatcher

from tactic_gen.lm_example import LmExample
from data_management.dataset_file import Sentence
from model_deployment.premise_model_wrapper import RerankWrapper

wrapper: Optional[RerankWrapper] = None


@dispatcher.add_method
def get_scores(context: str, premises: list[str]) -> list[float]:
    assert wrapper is not None
    return wrapper.get_premise_scores(context, premises)


@Request.application
def application(request: requests.models.Response):
    response = JSONRPCResponseManager.handle(request.data, dispatcher)
    return Response(response.json, mimetype="application/json")


if __name__ == "__main__":
    run_simple("localhost", 4000, application)
