
import sys, os
import json
import argparse

from flask import Flask, request

from tactic_gen.lm_example import LmExample 
from model_deployment.model_wrapper import CodeLLamaLocalWrapper, FORMAT_NAME, INFERENCE_NAME


app = Flask(__name__) 


#PRETRAINED_NAME = "/home/ubuntu/coq-modeling/models/codellama-7b-basic/checkpoint-20500"
PRETRAINED_NAME = "/home/ubuntu/coq-modeling/models/codellama-7b-premise/checkpoint-20500"
#PRETRAINED_NAME = "codellama/CodeLlama-7b-hf"

model_wrapper = CodeLLamaLocalWrapper.from_pretrained(PRETRAINED_NAME)

@app.route(FORMAT_NAME, methods=["POST"])
def format() -> str:
    example_config = model_wrapper.lm_example_config
    json_str = json.dumps(example_config.to_json(), indent=2)
    return json_str 


@app.route(INFERENCE_NAME, methods=["POST"])
def codellama() -> str:
    n = int(request.form["n"])
    example = LmExample.from_json(request.form)
    result = model_wrapper.get_recs(example, n)
    return json.dumps(result.to_json(), indent=2)


if __name__=="__main__":
    parser = argparse.ArgumentParser(description="Start a server running CodeLLama")    
    parser.add_argument("port", type=int, help="Port on which to run the server.")
    args = parser.parse_args(sys.argv[1:])
    app.run(host="0.0.0.0", port=args.port, debug=True, use_reloader=False)
