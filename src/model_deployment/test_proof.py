from __future__ import annotations
from typing import Any, Optional
import os
import json
import pdb
from dataclasses import dataclass
from pathlib import Path


from data_management.splits import FileInfo, Split, DataSplit, file_from_split
from data_management.dataset_file import FileContext, Term, Sentence
from model_deployment.searcher import (
    SearchTreeManager,
    SearchResult,
    SuccessfulSearch,
    FailedSearch,
)
from model_deployment.tactic_gen_client import TacticGenClientConf
from model_deployment.proof_manager import ProofManager
from model_deployment.node_score import NODE_SCORE_ALIASES

from data_management.sentence_db import SentenceDB
from util.util import get_basic_logger

from coqpyt.coq.structs import Step, TermType
from coqpyt.coq.proof_file import ProofFile
from coqpyt.coq.base_file import CoqFile

_logger = get_basic_logger(__name__)


@dataclass
class TestProofConf:
    test_file: Path
    data_loc: Path
    data_split_loc: Path
    theorem_name: str
    node_score_alias: str
    timeout: int
    branching_factor: int
    depth_limit: int
    max_exapansions: int
    tactic_client_conf: TacticGenClientConf

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> TestProofConf:
        return cls(
            Path(yaml_data["test_file"]),
            Path(yaml_data["data_loc"]),
            Path(yaml_data["data_split_loc"]),
            yaml_data["theorem_name"],
            yaml_data["node_score_alias"],
            yaml_data["timeout"],
            yaml_data["branching_factor"],
            yaml_data["depth_limit"],
            yaml_data["max_exapansions"],
            TacticGenClientConf.from_yaml(yaml_data["tactic_client_conf"]),
        )
    

def get_file_from_split(test_file: Path, data_loc: Path, data_split: DataSplit) -> Optional[FileInfo]:
    for split in Split:
        for file_info in data_split.get_file_list(split):
            info_path = data_loc / Path(file_info.file)
            if info_path.resolve() == test_file.resolve():
                return file_info
    return None


def get_dummy_file_info(test_file: Path) -> FileInfo:
    assert 0 < len(test_file.parents)
    repo = test_file.parents[0]
    dp_name = str(test_file).replace(os.path.sep, "-")
    return FileInfo(dp_name, str(test_file), str(repo), str(repo))


def test_proof(conf: TestProofConf):
    pass


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
    }
)
NODE_SCORE_TYPE = TokenLengthNormalizedScore
TIMEOUT = 600
BRANCH = 32
DEPTH_LIMIT=300
EXPANSIONS = 500



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

        _logger.debug("Beginning Proof Search")
        result = tree_manager.search(print_proofs=True, print_trees=True)
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

do_coq_file_search()
