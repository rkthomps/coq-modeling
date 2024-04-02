

import requests

from tactic_gen.lm_example import LmExample 
from model_deployment.model_result import ModelResult

class TacticGenClient:
    def __init__(self, url: str):
        self.url = url
    
    def get_recs(self, example: LmExample, n: int) -> ModelResult:
        request_data = {
            "method": "get_recs",
            "params": [example.to_json(), n],
            "jsonrpc": "2.0",
            "id": 0, 
        }
        response = requests.post(self.url, json=request_data).json()
        return ModelResult.from_json(response)
