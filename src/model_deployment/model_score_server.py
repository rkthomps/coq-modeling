from typing import Any, Optional
import sys, os
import argparse
from pathlib import Path
from werkzeug.wrappers import Request, Response
from werkzeug.serving import run_simple

import requests
from jsonrpc import JSONRPCResponseManager, dispatcher

from goal_evaluation.goal_example import GoalExample
from goal_evaluation.goal_wrapper import GoalWrapper
from model_deployment.model_result import ModelResult

wrapper: Optional[GoalWrapper] = None 

@dispatcher.add_method
def get_expected_n_left_and_score(example_json: GoalExample) -> Any:
    example = GoalExample.from_json(example_json)
    assert wrapper is not None
    n_left, score = wrapper.get_expected_n_left_and_score(example)
    return {
        "n_left": n_left,
        "score": score,
    }


@Request.application
def application(request: requests.models.Response):
    response = JSONRPCResponseManager.handle(request.data, dispatcher)
    return Response(response.json, mimetype="application/json")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("checkpoint_loc", help="Checkpoint of the goal wrapper")
    parser.add_argument("port", type=int, help="Port at which to host the model.")
    args = parser.parse_args(sys.argv[1:])
    wrapper = GoalWrapper.from_checkpoint(Path(args.checkpoint_loc))
    print("serving model at checkpoint ", args.port)
    run_simple("localhost", args.port, application)
