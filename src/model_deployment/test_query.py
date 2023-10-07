
from typing import Any 
import sys, os
import requests
import json
import pdb

import jsonlines

from model_deployment.searcher import ProofManager, SearchTreeManager
from model_deployment.model_wrapper import CodeLLamaServer, ModelWrapper, GPT4Wrapper 
from model_deployment.node_score import CodeLLamaNodeScore, NodeScore 
from tactic_gen.lm_example import LmExample, BasicLmExample, GPT4BasicLmExample, BaseCodeLLamaLmExample
from data_management.create_lm_dataset import LmExampleConfig 

# WRAPPER = GPT4Wrapper() 
# EXAMPLE_TYPE = GPT4BasicLmExample
# NODE_SCORE_TYPE = CodeLLamaNodeScore

WRAPPER = CodeLLamaServer("http://127.0.0.1:5000/codellama")
EXAMPLE_CONFIG = LmExampleConfig.from_example_type(BasicLmExample)
NODE_SCORE_TYPE = CodeLLamaNodeScore

# WRAPPER = CodeLLamaServer("http://127.0.0.1:5000/codellama")
# EXAMPLE_CONFIG = LmExampleConfig.from_example_type(BaseCodeLLamaLmExample)
# NODE_SCORE_TYPE = CodeLLamaNodeScore


#TEST_FILE = "/home/ubuntu/coq-modeling/test-coq-projs/harder_example.v"
TEST_FILE = "/home/ubuntu/coq-modeling/test-coq-projs/min.v"
#TEST_FILE = "/home/ubuntu/coq-modeling/test-coq-projs/lt_impl.v"
#TEST_FILE = "/home/ubuntu/coq-modeling/test-coq-projs/lt_trans.v"
TIMEOUT = 1000
BRANCH = 7 
EXPANSIONS = 30

with ProofManager(TEST_FILE, EXAMPLE_CONFIG) as proof_manager:
    tree_manager = SearchTreeManager(
        WRAPPER, proof_manager, NODE_SCORE_TYPE,
        BRANCH, EXPANSIONS,TIMEOUT 
    )

    result = tree_manager.search()
    with open("proof-tree.json", "w") as fout:
        json_proof_tree = result.search_tree.to_json()
        fout.write(json.dumps(json_proof_tree, indent=2))
    print(result.get_proof())