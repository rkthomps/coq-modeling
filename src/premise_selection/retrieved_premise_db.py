from __future__ import annotations
import json
from pathlib import Path
from typing import Optional, Any
from dataclasses import dataclass
from data_management.dataset_file import DatasetFile, Sentence
from data_management.sentence_db import SentenceDB

from proof_retrieval.retrieved_proof_db import StepID


@dataclass
class PremiseDBPage:
    step_to_premise_map: dict[StepID, list[Sentence]]

    def get(self, step_id: StepID) -> Optional[list[Sentence]]:
        return self.step_to_premise_map.get(step_id, [])

    def to_json(self, sentence_db: SentenceDB) -> Any:
        return {
            "step_to_premise_map": {
                key.to_string(): [val.to_json(sentence_db, False) for val in value]
                for key, value in self.step_to_premise_map.items()
            }
        }

    @classmethod
    def load(cls, path: Path, sentence_db: SentenceDB) -> PremiseDBPage:
        with open(path, "r") as fin:
            return cls.from_json(json.load(fin), sentence_db)

    @classmethod
    def from_json(cls, json_data: Any, sentence_db: Any) -> PremiseDBPage:
        return cls(
            {
                StepID.from_string(key): [
                    Sentence.from_json(val, sentence_db) for val in value
                ]
                for key, value in json_data["step_to_premise_map"].items()
            }
        )


@dataclass
class RetrievedPremiseDB:
    premise_db_loc: Path
    CONF_NAME = "premise_retriever_conf.yaml"

    def get_premises(
        self,
        step_idx: int,
        proof_idx: int,
        dset_file: DatasetFile,
        sentence_db: SentenceDB,
    ) -> Optional[list[Sentence]]:
        step_id = StepID.from_step_idx(step_idx, proof_idx, dset_file)
        page_loc = self.premise_db_loc / dset_file.dp_name
        page = PremiseDBPage.load(page_loc, sentence_db)
        return page.get(step_id)

    @classmethod
    def load(cls, path: Path) -> RetrievedPremiseDB:
        assert path.exists()
        assert (path / cls.CONF_NAME).exists()
        return cls(path)


if __name__ == "__main__":

    import os
    import shutil
    import yaml
    import argparse

    from concurrent.futures import ProcessPoolExecutor, Future, as_completed

    from model_deployment.conf_utils import (
        premise_conf_to_client_conf,
        wait_for_servers,
        start_servers,
    )

    from data_management.splits import FileInfo
    from model_deployment.rerank_client import (
        PremiseClient,
        PremiseConf,
        close_premise_client,
        premise_client_from_conf,
    )

    parser = argparse.ArgumentParser("Create a premise retrieval database.")
    parser.add_argument(
        "--premise_retriever_conf_loc",
        type=str,
        required=True,
        help="Path of the premise retriever config.",
    )
    parser.add_argument(
        "--save_loc", type=str, required=True, help="Path to save the premise database."
    )
    parser.add_argument(
        "--sentence_db_loc", type=str, required=True, help="Path to sentence database."
    )
    parser.add_argument("--premises_per_step", type=int, default=50)
    parser.add_argument(
        "--data_split_locs", type=str, nargs="+", help="Path to data splits."
    )
    args = parser.parse_args()

    # TODO

    def page_from_f_info(
        f_info: FileInfo,
        premise_conf: PremiseConf,
        data_loc: Path,
        sentence_db_loc: Path,
    ):
        sentence_db = SentenceDB.load(sentence_db_loc)
        premise_client = premise_client_from_conf(premise_conf)
        new_page_dict: dict[StepID, list[Sentence]] = {}
        f_dp = f_info.get_dp(data_loc, sentence_db)
        for proof_idx, proof in enumerate(f_dp.proofs):
            for step_idx, step in enumerate(proof.steps):
                step_id = StepID.from_step_idx(step_idx, proof_idx, f_dp)
                filter_result = (
                    premise_client.premise_filter.get_pos_and_avail_premises(
                        step, proof, f_dp
                    )
                )
                premise_generator = premise_client.get_ranked_premise_generator(
                    step, proof, f_dp, filter_result.avail_premises
                )

        sentence_db.close()
        close_premise_client(premise_client)
