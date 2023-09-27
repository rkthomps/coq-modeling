
from __future__ import annotations
from typing import Any

import sys, os
import json

from premise_selection.model import PremiseRetriever
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

class FormatResponse:
    def __init__(self, premise_format_alias: str, context_format_alias: str) -> None:
        assert type(premise_format_alias) == str
        assert type(context_format_alias) == str
        self.preise_format_alias = premise_format_alias
        self.context_format_alias = context_format_alias

    def to_json(self) -> Any:
        return {
            "premise_format_alias": self.preise_format_alias,
            "context_format_alias": self.context_format_alias,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> FormatResponse:
        premise_format_alias = json_data["premise_format_alias"]
        context_format_alias = json_data["context_format_alias"]
        return cls(premise_format_alias, context_format_alias)


FORMAT_ENDPOINT = "/formatters"
@app.route(FORMAT_ENDPOINT, methods=["POST"])
def formatters() -> str:
    format_response = FormatResponse(premise_format_alias, context_format_alias)
    return json.dumps(format_response.to_json(), indent=2)


class PremiseResponse:
    def __init__(self, premise_scores: list[float]) -> None:
        assert type(premise_scores) == list
        assert(all([float(p) for p in premise_scores]))
        self.premise_scores = premise_scores

    def to_json(self) -> Any:
        return {"premise_scores": self.premise_scores}

    @classmethod
    def from_json(cls, json_data: Any) -> PremiseResponse:
        premise_scores = json_data["premise_scores"]
        return cls(premise_scores)


PREMISE_ENDPOINT = "/premise"
@app.route(PREMISE_ENDPOINT, methods=["POST"])
def premise() -> str:
    context_str = request.form["context"]
    premise_list_json_str = request.form["premise_list"]
    premise_list = json.loads(premise_list_json_str)
    context_encoding = model.encode_str(context_str)
    premise_encodings: list[torch.Tensor] = []
    for premise_str in premise_list:
        premise_encoding = model.encode_str(premise_str)
        premise_encodings.append(premise_encoding)
    premise_matrix = torch.cat(premise_encodings)
    premise_scores = torch.mm(context_encoding, premise_matrix.t()) 
    premise_score_list = premise_scores.squeeze().tolist()
    premise_score_obj = PremiseResponse(premise_score_list)
    return json.dumps(premise_score_obj.to_json(), indent=2)


if __name__=="__main__":
    app.run(host="0.0.0.0", port=5000, debug=True, use_reloader=False)
