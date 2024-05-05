from __future__ import annotations
import os
from typing import Any, Optional
import json
import pickle
from dataclasses import dataclass
from pathlib import Path

from data_management.splits import FileInfo, Split, DataSplit
from data_management.dataset_file import Term, DatasetFile
from model_deployment.classical_searcher import ClassicalSuccess, ClassicalFailure
from model_deployment.mcts_searcher import MCTSSuccess, MCTSFailure
from model_deployment.prove import run_proof, RunProofConf, LocationInfo
from model_deployment.searcher import (
    SearcherConf,
    searcher_conf_from_yaml,
)

from model_deployment.tactic_gen_client import (
    TacticGenConf,
    tactic_gen_conf_from_yaml,
    tactic_gen_client_from_conf,
)

from data_management.sentence_db import SentenceDB
from util.util import get_basic_logger
from util.constants import CLEAN_CONFIG


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
    search_conf: SearcherConf
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
            searcher_conf_from_yaml(yaml_data["search"]),
            tactic_gen_conf_from_yaml(yaml_data["tactic_gen"]),
            yaml_data["print_proofs"],
            yaml_data["print_trees"],
        )



PROOF_KEYWORDS = ["Lemma", "Theorem", "Proposition", "Remark", "Example", "Property"]


def get_term(dp_file: DatasetFile, theorem_str: str) -> Term:
    for proof in dp_file.proofs:
        if proof.theorem.term.text.strip() == theorem_str.strip():
            return proof.theorem
    raise ValueError(f"{theorem_str} not found in {dp_file.file_context.file}")



if __name__ == "__main__":
    conf_loc = Path(f"./{CLEAN_CONFIG}")
    with conf_loc.open("rb") as fin:
        conf: TestProofConf = pickle.load(fin)
        assert "TestProofConf" in str(conf.__class__)  # isinstance didn't work
        result = run_proof(conf.to_run_conf())
        match result:
            case ClassicalSuccess():
                print("".join(result.qed_node.combined_proof_steps))
                print("depth", result.search_tree.root.get_deepest_node())
            case ClassicalFailure():
                print("failed")
            case MCTSSuccess():
                print(result.successful_proof.proof_text_to_string())
            case MCTSFailure():
                print("failed")
