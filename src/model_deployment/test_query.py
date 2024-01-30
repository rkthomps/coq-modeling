from typing import Any, Optional
import sys, os
import requests
import json
import pdb

from data_management.splits import FileInfo, Split
from model_deployment.searcher import (
    SearchTreeManager,
    SearchResult,
    SuccessfulSearch,
    FailedSearch,
)
from model_deployment.proof_manager import ProofManager, initialize_hidden_files
from model_deployment.model_wrapper import CodeLLamaServer, ModelWrapper, GPT4Wrapper
from model_deployment.node_score import (
    TokenLengthNormalizedScore,
    BranchNormalizedScore,
    LastTacGreedyScore,
    DepthFirstScore,
    BreadthFirstScore,
)
from util.util import get_basic_logger

from coqpyt.coq.proof_file import ProofFile
from coqpyt.coq.base_file import CoqFile

_logger = get_basic_logger(__name__)

# WRAPPER = GPT4Wrapper()
# EXAMPLE_TYPE = GPT4BasicLmExample
# NODE_SCORE_TYPE = CodeLLamaNodeScore


# WRAPPER = CodeLLamaServer("http://127.0.0.1:5000/codellama")
# EXAMPLE_CONFIG = LmExampleConfig.from_example_type(BaseCodeLLamaLmExample)
# NODE_SCORE_TYPE = CodeLLamaNodeScore

# TEST_FILE = "/home/ubuntu/coq-modeling/test-coq-projs/even_odd.v"
# TEST_FILE = "/home/ubuntu/coq-modeling/test-coq-projs/harder_example.v"
TEST_FILE = "/home/ubuntu/coq-modeling/test-coq-projs/example.v"
# TEST_FILE = "/home/ubuntu/coq-modeling/test-coq-projs/min.v"
# TEST_FILE = "/home/ubuntu/coq-modeling/test-coq-projs/lt_impl.v"
# TEST_FILE = "/home/ubuntu/coq-modeling/test-coq-projs/lt_trans.v"
# TEST_FILE = "/home/ubuntu/coq-modeling/examples/Adding/add_2.v"


dummy_file_info = FileInfo(
    "hi-dog",
    TEST_FILE,
    "/home/ubuntu/coq-modeling/examples",
    "/home/ubuntu/coq-modeling/examples",
)
dummy_split = Split.TEST
dummy_data_loc = "/"

with CoqFile(TEST_FILE, workspace=dummy_file_info.workspace) as coq_file:
    print("Initially valid: ", coq_file.is_valid)
    last: Optional[int] = None
    for i, step in enumerate(coq_file.steps):
        if "Theorem" in step.text or "Lemma" in step.text:
            last = i
assert last is not None


WRAPPER = CodeLLamaServer.from_conf({"server_url": "http://127.0.0.1:5000"})
NODE_SCORE_TYPE = TokenLengthNormalizedScore
TIMEOUT = 600
BRANCH = 4
EXPANSIONS = 500

_logger.debug("Creating Proof File")
with ProofFile(
    TEST_FILE, workspace=dummy_file_info.workspace, timeout=60
) as proof_file:
    proof_point = last
    _logger.debug("Creating Proof Manager")
    with ProofManager(
        TEST_FILE,
        proof_file,
        proof_point,
        WRAPPER.formatter,
        dummy_file_info,
        dummy_split,
        dummy_data_loc,
    ) as proof_manager:
        tree_manager = SearchTreeManager(
            WRAPPER, proof_manager, NODE_SCORE_TYPE, BRANCH, EXPANSIONS, TIMEOUT
        )

        _logger.debug("Beginning Proof Search")
        result = tree_manager.search(print_trees=True)
        with open("proof-tree.json", "w") as fout:
            json_proof_tree = result.search_tree.to_json()
            fout.write(json.dumps(json_proof_tree, indent=2))

        match result:
            case SuccessfulSearch():
                print(result.get_proof())
                qed_path = result.search_tree.root.get_path_to_qed()
                print(
                    (
                        f"Found proof after: {result.qed_node.creation_time / 1e9} seconds "
                        f"and {qed_path[-2].expanded} node expansions."
                    )
                )
            case FailedSearch():
                print("Failed Search")
