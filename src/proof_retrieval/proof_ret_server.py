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
from model_deployment.conf_utils import get_ip, get_free_port
from proof_retrieval.proof_ret_wrapper import ProofRetWrapper

wrapper: Optional[ProofRetWrapper] = None


@dispatcher.add_method
def get_scores(
    key_proof_str: str,
    avail_indices: list[int],
    key_proof_idx: int | None,
) -> list[float]:
    assert wrapper is not None
    return wrapper.get_scores(key_proof_str, avail_indices, key_proof_idx)


@Request.application
def application(request: requests.models.Response):
    response = JSONRPCResponseManager.handle(request.data, dispatcher)
    return Response(response.json, mimetype="application/json")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "model_name",
        help="Location of proof ret model checkpoint / name of the pretrained model.",
    )
    parser.add_argument("max_seq_len", type=int, help="Maximum sequence length.")
    parser.add_argument(
        "vector_db_loc", type=Path, help="Location of the proof vector db."
    )
    parser.add_argument("id", type=int, help="Model id (important for evaluation).")
    parser.add_argument("pid", type=int, help="Id of the parent process.")

    args = parser.parse_args(sys.argv[1:])

    vector_db_loc = Path(args.vector_db_loc)
    assert vector_db_loc.exists()
    wrapper = ProofRetWrapper.from_model_name(
        args.model_name, args.max_seq_len, vector_db_loc
    )

    id = args.id
    ip = get_ip()
    port = get_free_port()
    log.warning(f"SERVING AT {ip}; {port}")
    port_map_loc = get_port_map_loc(args.pid)
    assert port_map_loc.exists()

    with port_map_loc.open("a") as fout:
        fout.write(f"{id}\t{ip}\t{port}\n")
    run_simple(ip, port, application)
