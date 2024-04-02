from typing import Optional, Any
import argparse
from werkzeug.wrappers import Request, Response
from werkzeug.serving import run_simple

import requests
from jsonrpc import JSONRPCResponseManager, dispatcher

from tactic_gen.lm_example import LmExample
from data_management.dataset_file import Sentence
from model_deployment.premise_model_wrapper import SelectWrapper

wrapper: Optional[SelectWrapper] = None


@dispatcher.add_method
def get_scores(
    context: str, idx_premises: list[int], other_premises_json: list[Any]
) -> list[float]:
    assert wrapper is not None
    other_premises = [
        Sentence.from_json(o, wrapper.sentence_db) for o in other_premises_json
    ]
    return wrapper.get_premise_scores(context, idx_premises, other_premises)


@Request.application
def application(request: requests.models.Response):
    response = JSONRPCResponseManager.handle(request.data, dispatcher)
    return Response(response.json, mimetype="application/json")


if __name__ == "__main__":
    run_simple("localhost", 4000, application)
