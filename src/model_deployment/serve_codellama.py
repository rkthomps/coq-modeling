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

app = Flask(__name__)


PRETRAINED_NAME = "/home/ubuntu/coq-modeling/models/codellama-7b-basic-rnd-split-rnd-samp/checkpoint-7459"
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
    return json.dumps(result.to_json(), indent=2)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Start a server running CodeLLama")
    parser.add_argument("port", type=int, help="Port on which to run the server.")
    args = parser.parse_args(sys.argv[1:])
    app.run(host="0.0.0.0", port=args.port, debug=True, use_reloader=False)
