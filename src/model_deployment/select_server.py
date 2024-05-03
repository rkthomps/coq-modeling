from typing import Optional, Any
import argparse
import sys, os
from pathlib import Path

from werkzeug.wrappers import Request, Response
from werkzeug.serving import run_simple
from util.constants import SERVER_LOC

import logging

log = logging.getLogger("werkzeug")
log.setLevel(logging.ERROR)

import requests
from jsonrpc import JSONRPCResponseManager, dispatcher

from tactic_gen.lm_example import LmExample
from data_management.dataset_file import Sentence
from model_deployment.premise_model_wrapper import SelectWrapper

wrapper: Optional[SelectWrapper] = None


@dispatcher.add_method
def set_transform_mat(premises_json: list[Sentence], contexts_json: list[str]) -> None:
    assert wrapper is not None
    ps = [Sentence.from_json(p, wrapper.sentence_db) for p in premises_json]
    wrapper.set_transformation_matrix(ps, contexts_json)


@dispatcher.add_method
def clear_transform_mat() -> None:
    assert wrapper is not None
    wrapper.clear_transformation_matrix()


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
    parser = argparse.ArgumentParser()
    parser.add_argument("checkpoint_loc", help="Location of select model checkpoint.")
    parser.add_argument("--vector_db_loc", help="Location of vector database.")
    parser.add_argument(
        "port", type=int, help="Port on which to run the select server."
    )
    args = parser.parse_args(sys.argv[1:])
    wrapper = SelectWrapper.from_checkpoint(args.checkpoint_loc, args.vector_db_loc)
    serve_path = (Path(f"./{SERVER_LOC}") / str(args.port)).resolve()
    run_simple(f"unix://{serve_path}", args.port, application)
