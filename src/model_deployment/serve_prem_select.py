from __future__ import annotations
from typing import Any

import sys, os
import json

from premise_selection.model import PremiseRetriever
from model_deployment.serve_prem_utils import (
    FormatResponse,
    PremiseRequest,
    PremiseResponse,
    FORMAT_ENDPOINT,
    PREMISE_ENDPOINT,
)
from model_deployment.premise_model_wrapper import SelectWrapper
from data_management.create_premise_dataset import PREMISE_DATA_CONF_NAME

from yaml import load, Loader
from flask import Flask, request
import torch

app = Flask(__name__)

# CHECKPOINT_LOC = "/home/ubuntu/coq-modeling/models/premise_selection_basic/lightning_logs/version_0/checkpoints/epoch=2-step=55287.ckpt"
CHECKPOINT_LOC = "/home/kthompson/coq-modeling/models/prem-select/checkpoint-13683"


model_wrapper = SelectWrapper.from_checkpoint(CHECKPOINT_LOC)


@app.route(FORMAT_ENDPOINT, methods=["POST"])
def formatters() -> str:
    context_format_alias = model_wrapper.context_format.get_alias()
    premise_format_alias = model_wrapper.premise_format.get_alias()
    premise_filter_json = model_wrapper.premise_filter.to_json()
    format_response = FormatResponse(
        context_format_alias, premise_format_alias, premise_filter_json
    )
    return json.dumps(format_response.to_json(), indent=2)


@app.route(PREMISE_ENDPOINT, methods=["POST"])
def premise() -> str:
    selection_request = PremiseRequest.from_request_data(dict(request.form))
    premise_score_list = model_wrapper.get_premise_scores_from_strings(
        selection_request.context, selection_request.premises
    )
    premise_score_obj = PremiseResponse(premise_score_list)
    return json.dumps(premise_score_obj.to_json(), indent=2)


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=5000, debug=True, use_reloader=False)
