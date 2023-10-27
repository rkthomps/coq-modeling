from typing import Any
import sys, os
import requests
import json
import pdb

import jsonlines

from model_deployment.searcher import SearchTreeManager
from model_deployment.proof_manager import ProofManager, initialize_hidden_files
from model_deployment.model_wrapper import CodeLLamaServer, ModelWrapper, GPT4Wrapper
from model_deployment.node_score import (
    TokenLengthNormalizedScore,
    BranchNormalizedScore,
    DepthFirstScore,
    BreadthFirstScore,
)
from tactic_gen.lm_example import (
    LmExample,
    BasicLmExample,
    GPT4BasicLmExample,
    BaseCodeLLamaLmExample,
)
from data_management.create_lm_dataset import LmExampleConfig

from coqlspclient.proof_file import ProofFile

# WRAPPER = GPT4Wrapper()
# EXAMPLE_TYPE = GPT4BasicLmExample
# NODE_SCORE_TYPE = CodeLLamaNodeScore

WRAPPER = CodeLLamaServer.from_url("http://127.0.0.1:5000")
NODE_SCORE_TYPE = TokenLengthNormalizedScore

# WRAPPER = CodeLLamaServer("http://127.0.0.1:5000/codellama")
# EXAMPLE_CONFIG = LmExampleConfig.from_example_type(BaseCodeLLamaLmExample)
# NODE_SCORE_TYPE = CodeLLamaNodeScore

TEST_FILE = "/home/ubuntu/coq-modeling/test-coq-projs/harder_example.v"
# TEST_FILE = "/home/ubuntu/coq-modeling/test-coq-projs/min.v"
# TEST_FILE = "/home/ubuntu/coq-modeling/test-coq-projs/lt_impl.v"
# TEST_FILE = "/home/ubuntu/coq-modeling/test-coq-projs/lt_trans.v"


TIMEOUT = 600
BRANCH = 4
EXPANSIONS = 500

hidden_file_path, aux_hidden_file_path = initialize_hidden_files(TEST_FILE)
with ProofFile(hidden_file_path, timeout=60) as proof_file:
    with ProofManager(
        hidden_file_path, proof_file, aux_hidden_file_path, WRAPPER.lm_example_config
    ) as proof_manager:
        tree_manager = SearchTreeManager(
            WRAPPER, proof_manager, NODE_SCORE_TYPE, BRANCH, EXPANSIONS, TIMEOUT
        )

        result = tree_manager.search(print_trees=True)
        with open("proof-tree.json", "w") as fout:
            json_proof_tree = result.search_tree.to_json()
            fout.write(json.dumps(json_proof_tree, indent=2))

        if result.found_proof():
            assert result.qed_node is not None
            print(result.get_proof())
            qed_path = result.search_tree.get_path_to_qed()
            print(
                (
                    f"Found proof after: {result.qed_node.creation_time / 1e9} seconds "
                    f"and {qed_path[-2].expanded} node expansions."
                )
            )
