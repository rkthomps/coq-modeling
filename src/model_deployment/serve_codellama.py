from typing import Optional

import sys, os
import json
import argparse

from flask import Flask, request

from tactic_gen.lm_example import LmExample, fmt_get_conf
from model_deployment.model_wrapper import (
    CodeLLamaLocalWrapper,
    FORMAT_NAME,
    INFERENCE_NAME,
    wrapper_from_conf,
)
from util.util import get_basic_logger

app = Flask(__name__)
_logger = get_basic_logger(__name__)

# PRETRAINED_NAME = "/home/ubuntu/coq-modeling/models/codellama-7b-tpe-1k-rnd-split-rnd-samp-pct-8/checkpoint-4133"
# PRETRAINED_NAME = "/home/ubuntu/coq-modeling/models/codellama-7b-prf-oracle-rnd-split-rnd-samp-pct-8/checkpoint-4139"
PRETRAINED_NAME = "/home/ubuntu/coq-modeling/models/codellama-7b-premise-no-coq-rnd-split-rnd-samp-pct-8/checkpoint-4306"
local_conf = {
    "alias": CodeLLamaLocalWrapper.ALIAS,
    "pretrained-name": PRETRAINED_NAME,
}

model_wrapper = wrapper_from_conf(local_conf)


@app.route(FORMAT_NAME, methods=["POST"])
def format() -> str:
    json_str = json.dumps(fmt_get_conf(model_wrapper.formatter), indent=2)
    return json_str


@app.route(INFERENCE_NAME, methods=["POST"])
def codellama() -> str:
    n = int(request.form["n"])
    example = LmExample.from_json(request.form)
    result = model_wrapper.get_recs(example, n)
    _logger.debug(f"Input {example.input}")
    return json.dumps(result.to_json(), indent=2)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Start a server running CodeLLama")
    parser.add_argument("port", type=int, help="Port on which to run the server.")
    args = parser.parse_args(sys.argv[1:])
    app.run(host="0.0.0.0", port=args.port, debug=True, use_reloader=False)
