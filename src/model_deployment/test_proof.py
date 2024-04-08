from __future__ import annotations
from typing import Any, Optional
import json
import pickle
from dataclasses import dataclass
from pathlib import Path

from data_management.splits import FileInfo, Split, DataSplit
from data_management.dataset_file import Term, DatasetFile
from model_deployment.searcher import (
    SearchTreeManager,
    SuccessfulSearch,
    FailedSearch,
)
from model_deployment.tactic_gen_client import TacticGenConf, TacticGenClient
from model_deployment.proof_manager import ProofManager, ProofInfo
from model_deployment.node_score import NODE_SCORE_ALIASES

from data_management.sentence_db import SentenceDB
from util.util import get_basic_logger
from util.constants import CLEAN_CONFIG

from coqpyt.coq.base_file import CoqFile

_logger = get_basic_logger(__name__)


@dataclass
class TestProofConf:
    test_file: Path
    data_loc: Path
    sentence_db_loc: Path
    data_split_loc: Path
    theorem_name: str
    node_score_alias: str
    timeout: int
    branching_factor: int
    depth_limit: int
    max_exapansions: int
    tactic_conf: TacticGenConf 

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> TestProofConf:
        return cls(
            Path(yaml_data["test_file"]),
            Path(yaml_data["sentence_db_loc"]),
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


def get_file_from_split(
    test_file: Path, data_loc: Path, data_split: DataSplit
) -> Optional[tuple[FileInfo, Split]]:
    for split in Split:
        for file_info in data_split.get_file_list(split):
            info_path = data_loc / Path(file_info.file)
            if info_path.resolve() == test_file.resolve():
                return file_info, split
    return None


PROOF_KEYWORDS = ["Lemma", "Theorem", "Proposition", "Remark", "Example", "Property"]


def get_term(dp_file: DatasetFile, theorem_str: str) -> Term:
    for proof in dp_file.proofs:
        if proof.theorem.term.text == theorem_str:
            return proof.theorem
    raise ValueError(f"{theorem_str} not found in {dp_file.file_context.file}")


def get_proof_info(
    file_info: FileInfo, dp_file: DatasetFile, theorem_name: str
) -> ProofInfo:
    file_loc = Path(file_info.file).resolve()
    workspace_loc = Path(file_info.workspace).resolve()
    with CoqFile(str(file_loc), workspace=str(workspace_loc)) as coq_file:
        for i, step in enumerate(coq_file.steps):
            if (
                any([k in step.text for k in PROOF_KEYWORDS])
                and theorem_name in step.text
            ):
                term = get_term(dp_file, step.text)
                return ProofInfo(term, coq_file.steps[: (i + 1)], i)
    raise ValueError(f"Could not find step defining theorem {theorem_name}")


def test_proof(conf: TestProofConf):
    data_split = DataSplit.load(conf.data_split_loc)
    sentence_db = SentenceDB.load(conf.sentence_db_loc)
    file_info_tup = get_file_from_split(conf.test_file, conf.data_loc, data_split)
    assert file_info_tup is not None  # TODO Support unknown files
    file_info, split = file_info_tup
    file_dp = file_info.get_dp(conf.data_loc, sentence_db)
    tactic_client = TacticGenClient.from_conf(conf.tactic_conf)
    proof_info = get_proof_info(file_info, file_dp, conf.theorem_name)
    with ProofManager(
        file_dp.file_context,
        proof_info,
        tactic_client.formatter,
        file_info,
        sentence_db,
        split,
        conf.data_loc,
    ) as proof_manager:
        tree_manager = SearchTreeManager(
            tactic_client,
            proof_manager, 
            NODE_SCORE_ALIASES[conf.node_score_alias],
            conf.branching_factor,
            conf.max_exapansions,
            conf.depth_limit,
            conf.timeout,
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


if __name__ == "__main__":
    conf_loc = Path(f"./{CLEAN_CONFIG}") 
    with conf_loc.open("rb") as fin:
        conf = pickle.load(fin)
        assert isinstance(conf, TestProofConf)
        test_proof(conf)
