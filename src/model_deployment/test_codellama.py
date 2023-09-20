
from typing import Any 
import sys, os
import requests
import json
import pdb

import jsonlines

from model_deployment.searcher import ProofManager, SearchTreeManager
from model_deployment.model_wrapper import CodeLLamaNodeScore, CodeLLamaServer
from data_management.lm_example import LmExample, BasicLmExample


if __name__ == "__main__":
    #file_path = "/home/ubuntu/coq-modeling/test-coq-projs/min.v"
    file_path = "/home/ubuntu/coq-modeling/test-coq-projs/harder_example.v"
    server_url = "http://127.0.0.1:5000/codellama"
    proof_manager = ProofManager(file_path, BasicLmExample)
    node_score_type = CodeLLamaNodeScore
    tree_manager = SearchTreeManager(
        CodeLLamaServer(server_url), proof_manager, node_score_type,
        4, 30, 100
    )
    result = tree_manager.search()
    proof_manager.close()
    print(result.get_proof())