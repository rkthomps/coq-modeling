
import requests
import json

from data_management.lm_example import LmExample


class ModelResult:
    def __init__(self, 
                 next_tactic_list: list[str], 
                 score_list: [list[float]]) -> None:
        assert all([type(t) == str for t in next_tactic_list])
        assert all([type(s) == float for s in score_list]) 
        self.next_tactic_list = next_tactic_list
        self.score_list = score_list


class ModelWrapper:
    def get_recs(self, example: LmExample) -> ModelResult:
        raise NotImplementedError


class CodeLLamaServer(ModelWrapper):
    def __init__(self, server_url: str) -> None:
        self.server_url = server_url

    def get_recs(self, example: LmExample) -> ModelResult:
        response = requests.post(self.server_url, example.to_json())
        response_data = json.loads(response.content)
        





