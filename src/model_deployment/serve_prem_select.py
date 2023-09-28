
from __future__ import annotations
from typing import Any

import sys, os
import json

from premise_selection.model import PremiseRetriever
from model_deployment.serve_prem_utils import (
    FormatResponse, PremiseRequest, PremiseResponse, FORMAT_ENDPOINT, PREMISE_ENDPOINT)
from data_management.create_premise_dataset import PREMISE_CONFIG_NAME 

from yaml import load, Loader
from flask import Flask, request
import torch

app = Flask(__name__) 

MODEL_LOC = "/home/ubuntu/coq-modeling/models/premise_selection_basic"
CHECKPOINT_NAME = "epoch=2-step=55287.ckpt"

model = PremiseRetriever.load_from_conf_and_checkpoint(MODEL_LOC, CHECKPOINT_NAME)
embedding_cache: dict[str, torch.Tensor] = []

model_conf_loc = os.path.join(MODEL_LOC, "config.yaml")
with open(model_conf_loc, "r") as fin:
    model_conf = load(fin, Loader=Loader)
training_data_loc = model_conf["data"]["premise_data_path"]
data_preparation_conf = os.path.join(training_data_loc, PREMISE_CONFIG_NAME)
with open(data_preparation_conf, "r") as fin:
    premise_conf = load(fin, Loader=Loader)
premise_format_alias = premise_conf["premise_format_alias"]
context_format_alias = premise_conf["context_format_alias"]


@app.route(FORMAT_ENDPOINT, methods=["POST"])
def formatters() -> str:
    format_response = FormatResponse(premise_format_alias, context_format_alias)
    return json.dumps(format_response.to_json(), indent=2)


embedding_cache: dict[str, torch.Tensor] = {}

def get_encoding(to_encode: str) -> torch.Tensor:
    if to_encode in embedding_cache:
        return embedding_cache[to_encode]
    encoding = model.encode_str(to_encode)
    embedding_cache[to_encode] = encoding
    return encoding 

@app.route(PREMISE_ENDPOINT, methods=["POST"])
def premise() -> str:
    selection_request = PremiseRequest.from_request_data(request.form)
    context_encoding = get_encoding(selection_request.context)
    premise_encodings: list[torch.Tensor] = []
    for premise_str in selection_request.premises:
        premise_encoding = get_encoding(premise_str)
        premise_encodings.append(premise_encoding)
    premise_matrix = torch.cat(premise_encodings)
    premise_scores = torch.mm(context_encoding, premise_matrix.t()) 
    premise_score_list = premise_scores.squeeze().tolist()
    premise_score_obj = PremiseResponse(premise_score_list)
    return json.dumps(premise_score_obj.to_json(), indent=2)


if __name__=="__main__":
    app.run(host="0.0.0.0", port=5000, debug=True, use_reloader=False)
