

import requests
import json

from premise_selection.premise_formatter import (
    PremiseFormat, PREMISE_ALIASES, ContextFormat, CONTEXT_ALIASES)
from model_deployment.serve_prem_select import (
    FORMAT_ENDPOINT, PREMISE_ENDPOINT, FormatResponse, PremiseResponse)

URL = "http://127.0.0.1:5000"

format_endpoint = URL + FORMAT_ENDPOINT
premise_endpoint = URL + PREMISE_ENDPOINT 

format_response = requests.post(format_endpoint, {})
format_response_dict = json.loads(format_response.content)
format_obj = FormatResponse.from_json(format_response_dict)

# TODO: ACCESS context through proof manager to get premise selection ex.

