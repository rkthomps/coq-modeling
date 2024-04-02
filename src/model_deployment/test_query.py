from typing import Any, Optional
import sys, os
import requests
import cProfile
import json
import logging
import pdb

from data_management.splits import FileInfo, Split
from data_management.dataset_file import FileContext, Term, Sentence
from model_deployment.searcher import (
    SearchTreeManager,
    SearchResult,
    SuccessfulSearch,
    FailedSearch,
)
from model_deployment.proof_manager import ProofManager
from model_deployment.model_node_scorer import ModelNodeScorer
from model_deployment.model_wrapper import (
    CodeLLamaServer,
    FidT5LocalWrapper,
    ModelWrapper,
    GPT4Wrapper,
)
from model_deployment.node_score import (
    TokenLengthNormalizedScore,
    ModelScore,
    TokenSumScore,
    BranchNormalizedScore,
    LastTacGreedyScore,
    DepthFirstScore,
    BreadthFirstScore,
)
from data_management.sentence_db import SentenceDB
from util.util import LOGGER

from coqpyt.coq.structs import Step, TermType
from coqpyt.coq.proof_file import ProofFile
from coqpyt.coq.base_file import CoqFile



# WRAPPER = GPT4Wrapper()
# EXAMPLE_TYPE = GPT4BasicLmExample
# NODE_SCORE_TYPE = CodeLLamaNodeScore


# WRAPPER = CodeLLamaServer("http://127.0.0.1:5000/codellama")
# EXAMPLE_CONFIG = LmExampleConfig.from_example_type(BaseCodeLLamaLmExample)
# NODE_SCORE_TYPE = CodeLLamaNodeScore

#TEST_FILE = "/home/ubuntu/coq-modeling/test-coq-projs/even_odd.v"
#TEST_FILE = "/home/ubuntu/coq-modeling/test-coq-projs/harder_example.v"
#TEST_FILE = "/home/ubuntu/coq-modeling/test-coq-projs/example.v"
#TEST_FILE = "/home/ubuntu/coq-modeling/test-coq-projs/min.v"
#TEST_FILE = "/home/ubuntu/coq-modeling/test-coq-projs/lt_impl.v"
#TEST_FILE = "/home/ubuntu/coq-modeling/test-coq-projs/lt_trans.v"
# TEST_FILE = "/home/ubuntu/coq-modeling/examples/Adding/add_2.v"
TEST_FILE = "/home/ubuntu/coq-modeling/test-coq-projs/min_superlist.v"


dummy_file_info = FileInfo(
    "hi-dog",
    TEST_FILE,
    "/home/ubuntu/coq-modeling/test-coq-projs",
    "/home/ubuntu/coq-modeling/test-coq-projs",
)
dummy_split = Split.TEST
dummy_data_loc = "/"

sentence_db = SentenceDB.load("./sentences.db") 

# WRAPPER = CodeLLamaServer.from_conf({"server_url": "http://127.0.0.1:5000"})
WRAPPER = FidT5LocalWrapper.from_conf(
    {
        # "alias": "fid-local",
        # "pretrained_name": "/home/ubuntu/coq-modeling/models/t5-fid-small-basic-rnd-split-rnd-samp-pct-8/checkpoint-8000"
        "pretrained-name": "/home/ubuntu/coq-modeling/models/t5-fid-base-basic-final/checkpoint-110500"
        #"pretrained-name": "/home/ubuntu/coq-modeling/models/t5-fid-small-basic-final/checkpoint-110500"
    }
)
NODE_SCORE_TYPE = TokenLengthNormalizedScore
#NODE_SCORE_TYPE = ModelScore 
TIMEOUT = 600
#BRANCH = 256
BRANCH = 64 
DEPTH_LIMIT=300
EXPANSIONS = 500
#MODEL_SCORER = ModelNodeScorer.from_name("codellama/CodeLlama-7b-hf")
MODEL_SCORER = None


def do_search(file_context: FileContext, initial_steps: list[Step], proof_point: int, proof_term: Term):
    with ProofManager(
        TEST_FILE,
        file_context,
        proof_term,
        initial_steps,
        proof_point,
        WRAPPER.formatter,
        dummy_file_info,
        sentence_db,
        dummy_split,
        dummy_data_loc,
    ) as proof_manager:
        tree_manager = SearchTreeManager(
            WRAPPER, proof_manager, NODE_SCORE_TYPE, BRANCH, EXPANSIONS, DEPTH_LIMIT, TIMEOUT, MODEL_SCORER 
    )

        LOGGER.debug("Beginning Proof Search")
        result = tree_manager.search(print_proofs=True, print_trees=False)
        with open("proof-tree.json", "w") as fout:
            json_proof_tree = result.search_tree.to_json(proof_manager.sentence_db)
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


def do_coq_file_search():
    file = os.path.abspath(dummy_file_info.file)
    workspace = os.path.abspath(dummy_file_info.workspace)
    file_context = FileContext(file, workspace, dummy_file_info.repository, [])
    with CoqFile(TEST_FILE, workspace=dummy_file_info.workspace) as coq_file:
        print("Initially valid: ", coq_file.is_valid)
        last: Optional[int] = None
        for i, step in enumerate(coq_file.steps):
            if "Theorem" in step.text or "Lemma" in step.text:
                last = i
        assert last is not None
        initial_steps = coq_file.steps[:(last + 1)]
    theorem_sentence = Sentence(initial_steps[-1].text, file, [], TermType.LEMMA, initial_steps[-1].ast.range.start.line)
    term = Term(theorem_sentence, [])
    do_search(file_context, initial_steps, last, term)


def do_proof_file_search():
    ## TODO
    pass

cProfile.run("do_coq_file_search()")
