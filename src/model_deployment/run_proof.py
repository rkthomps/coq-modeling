from __future__ import annotations
import os
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
from model_deployment.tactic_gen_client import (
    TacticGenConf,
    TacticGenClient,
    tactic_gen_conf_from_yaml,
    tactic_gen_client_from_conf,
)
from model_deployment.proof_manager import ProofInfo, ProofManager
from model_deployment.searcher import SearchConf, SuccessfulSearch, FailedSearch

from data_management.sentence_db import SentenceDB
from util.util import get_basic_logger
from util.constants import CLEAN_CONFIG

from coqpyt.coq.base_file import CoqFile

_logger = get_basic_logger(__name__)


@dataclass
class TheoremLocationInfo:
    theorem_name: str
    test_file: Path
    data_loc: Path
    sentence_db_loc: Path
    data_split_loc: Path

    def get_file_from_split(
        self,
        data_split: DataSplit,
    ) -> tuple[FileInfo, Split]:
        for split in Split:
            for file_info in data_split.get_file_list(split):
                info_path = self.data_loc / Path(file_info.file)
                if info_path.resolve() == self.test_file.resolve():
                    return file_info, split
        raise ValueError(
            f"Could not find data points file corresponding to {self.test_file}"
        )

    def get_dp_idx(self, dp: DatasetFile) -> int:
        _logger.warning("TODO DO THEOREM NAME MATCHING RIGHT")
        for i, proof in enumerate(dp.proofs):
            if self.theorem_name in proof.theorem.term.text:
                return i
        raise ValueError(f"{self.theorem_name} not found in {self.test_file}")
    
    def to_location_info(self) -> LocationInfo:
        data_split = DataSplit.load(self.data_split_loc)
        file_info, split = self.get_file_from_split(data_split)
        sentence_db = SentenceDB.load(self.sentence_db_loc)
        file_dp = file_info.get_dp(self.data_loc, sentence_db)
        idx = self.get_dp_idx(file_dp)
        return LocationInfo(
            self.data_loc, file_info, split, file_dp, idx, sentence_db, data_split 
        )

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> TheoremLocationInfo:
        return cls(
            yaml_data["theorem_name"],
            Path(yaml_data["test_file"]),
            Path(yaml_data["data_loc"]),
            Path(yaml_data["sentence_db_loc"]),
            Path(yaml_data["data_split_loc"]),
        )


@dataclass
class TestProofConf:
    theorem_location_info: TheoremLocationInfo
    search_conf: SearchConf
    tactic_conf: TacticGenConf
    print_proofs: bool
    print_trees: bool


    def to_run_conf(self) -> RunProofConf:
        return RunProofConf(
            self.theorem_location_info.to_location_info(),
            self.search_conf,
            tactic_gen_client_from_conf(self.tactic_conf),
            self.print_proofs,
            self.print_trees,
        )

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> TestProofConf:
        return cls(
            TheoremLocationInfo.from_yaml(yaml_data["thm_info"]),
            SearchConf.from_yaml(yaml_data["search"]),
            tactic_gen_conf_from_yaml(yaml_data["tactic_gen"]),
            yaml_data["print_proofs"],
            yaml_data["print_trees"],
        )


@dataclass
class LocationInfo:
    data_loc: Path
    file_info: FileInfo
    split: Split
    dataset_file: DatasetFile
    dp_proof_idx: int
    sentence_db: SentenceDB
    data_split: DataSplit


@dataclass
class RunProofConf:
    location_info: LocationInfo
    search_conf: SearchConf
    tactic_gen: TacticGenClient
    print_proofs: bool
    print_trees: bool


PROOF_KEYWORDS = ["Lemma", "Theorem", "Proposition", "Remark", "Example", "Property"]


def get_term(dp_file: DatasetFile, theorem_str: str) -> Term:
    for proof in dp_file.proofs:
        if proof.theorem.term.text.strip() == theorem_str.strip():
            return proof.theorem
    raise ValueError(f"{theorem_str} not found in {dp_file.file_context.file}")


def normalize(s: str) -> str:
    return " ".join(s.split())


def get_proof_info(
    data_loc: Path,
    file_info: FileInfo,
    term: Term,
) -> ProofInfo:
    file_loc = (data_loc / file_info.file).resolve()
    workspace_loc = (data_loc / file_info.workspace).resolve()
    with CoqFile(str(file_loc), workspace=str(workspace_loc)) as coq_file:
        for i, step in enumerate(coq_file.steps):
            if normalize(step.text) in normalize(term.term.text) or normalize(
                term.term.text
            ) in normalize(step.text):
                return ProofInfo(term, coq_file.steps[: (i + 1)], i)
    raise ValueError(f"Could not find step defining theorem {term.term.text}")


def run_proof(conf: RunProofConf) -> SuccessfulSearch | FailedSearch:
    proof_info = get_proof_info(
        conf.location_info.data_loc,
        conf.location_info.file_info,
        conf.location_info.dataset_file.proofs[conf.location_info.dp_proof_idx].theorem,
    )
    with ProofManager(
        conf.location_info.dataset_file.file_context,
        proof_info,
        conf.tactic_gen.formatter,
        conf.location_info.file_info,
        conf.location_info.sentence_db,
        conf.location_info.split,
        conf.location_info.data_loc,
    ) as proof_manager:
        tree_manager = SearchTreeManager.from_conf(
            conf.search_conf, conf.tactic_gen, proof_manager
        )
        result = tree_manager.search(
            print_proofs=conf.print_proofs, print_trees=conf.print_trees
        )
        return result


if __name__ == "__main__":
    conf_loc = Path(f"./{CLEAN_CONFIG}")
    with conf_loc.open("rb") as fin:
        conf: TestProofConf = pickle.load(fin)
        assert "TestProofConf" in str(conf.__class__)  # isinstance didn't work
        result = run_proof(conf.to_run_conf())
        match result:
            case SuccessfulSearch():
                print("".join(result.qed_node.combined_proof_steps))
                print("depth", result.search_tree.root.get_deepest_node())
            case FailedSearch():
                print("failed")
