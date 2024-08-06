from __future__ import annotations
from typing import Any, Optional
import json
from pathlib import Path

import argparse
from dataclasses import dataclass

from data_management.sentence_db import SentenceDB
from data_management.splits import DataSplit, get_all_files, FileInfo
from data_management.dataset_file import DatasetFile

from util.util import get_basic_logger


_logger = get_basic_logger(__name__)


@dataclass
class StepID:
    file: str
    proof_idx: int
    step_idx: int

    def __hash__(self) -> int:
        return hash((self.file, self.proof_idx, self.step_idx))

    def to_string(self) -> str:
        return json.dumps(self.to_json())

    def to_json(self) -> Any:
        return {
            "file": self.file,
            "proof_idx": self.proof_idx,
            "step_idx": self.step_idx,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> StepID:
        return cls(
            json_data["file"],
            json_data["proof_idx"],
            json_data["step_idx"],
        )

    @classmethod
    def from_string(cls, s: str) -> StepID:
        return cls.from_json(json.loads(s))

    @classmethod
    def from_step_idx(
        cls, step_idx: int, proof_idx: int, dset_file: DatasetFile
    ) -> StepID:
        return StepID(dset_file.dp_name, proof_idx, step_idx)


@dataclass
class ProofDBPage:
    step_to_proof_map: dict[StepID, list[StepID]]

    def get(self, step_id: StepID) -> Optional[list[StepID]]:
        return self.step_to_proof_map.get(step_id)

    def to_json(self) -> Any:
        return {
            "step_to_proof_map": {
                key.to_string(): [val.to_string() for val in value]
                for key, value in self.step_to_proof_map.items()
            }
        }

    @classmethod
    def load(cls, path: Path) -> ProofDBPage:
        with open(path, "r") as f:
            return cls.from_json(json.load(f))

    @classmethod
    def from_json(cls, json_data: Any) -> ProofDBPage:
        return cls(
            {
                StepID.from_string(key): [StepID.from_string(val) for val in value]
                for key, value in json_data["step_to_proof_map"].items()
            }
        )


@dataclass
class RetrievedProofDB:
    proof_db_loc: Path
    CONF_NAME = "proof_retriever_conf.yaml"

    def get_steps(
        self, step_idx: int, proof_idx: int, dset_file: DatasetFile
    ) -> Optional[list[StepID]]:
        step_id = StepID.from_step_idx(step_idx, proof_idx, dset_file)
        page_loc = self.proof_db_loc / dset_file.dp_name
        page = ProofDBPage.load(page_loc)
        return page.get(step_id)

    def add_page(self, page: ProofDBPage, dset_file: DatasetFile):
        with open(self.proof_db_loc / dset_file.dp_name, "w") as f:
            json.dump(page.to_json(), f, indent=2)

    @classmethod
    def load(cls, path: Path) -> RetrievedProofDB:
        assert path.exists()
        assert (path / cls.CONF_NAME).exists()
        return cls(path)


if __name__ == "__main__":
    """
    The main method of this class runs a single worker.
    """
    import os
    import shutil
    import yaml
    import time
    import queue
    import multiprocessing as mp
    from proof_retrieval.proof_retriever import (
        ProofRetrieverConf,
        proof_retriever_conf_from_yaml,
        proof_retriever_from_conf,
        close_proof_retriever,
    )
    from concurrent.futures import ProcessPoolExecutor, Future, as_completed

    from model_deployment.conf_utils import (
        proof_conf_to_client_conf,
        wait_for_servers,
        start_servers,
    )

    parser = argparse.ArgumentParser("Create a proof retrieval database.")
    parser.add_argument(
        "--proof_retriever_conf_loc",
        type=str,
        required=True,
        help="Path of the proof retriever config.",
    )
    parser.add_argument(
        "--save_loc", type=str, required=True, help="Path to save the proof database."
    )
    parser.add_argument(
        "--data_loc", type=str, required=True, help="Path to CoqStoq dataset."
    )
    parser.add_argument(
        "--sentence_db_loc", type=str, required=True, help="Path to sentence database."
    )
    parser.add_argument("--num_workers", type=int, default=1, help="Number of workers.")
    parser.add_argument(
        "--data_split_locs",
        type=str,
        required=True,
        nargs="+",
        help="Path to data splits.",
    )

    args = parser.parse_args()

    proof_retriever_conf_loc = Path(args.proof_retriever_conf_loc)
    save_loc = Path(args.save_loc)
    data_loc = Path(args.data_loc)
    sentence_db_loc = Path(args.sentence_db_loc)
    num_workers = args.num_workers

    data_split_locs: list[Path] = [Path(loc) for loc in args.data_split_locs]
    assert all(loc.exists() for loc in data_split_locs)
    data_splits = [DataSplit.load(loc) for loc in data_split_locs]

    assert proof_retriever_conf_loc.exists()
    assert data_loc.exists()
    assert sentence_db_loc.exists()

    if save_loc.exists():
        raise FileExistsError(f"{args.save_loc} already exists.")
    os.makedirs(save_loc)
    shutil.copy(proof_retriever_conf_loc, save_loc / RetrievedProofDB.CONF_NAME)

    with proof_retriever_conf_loc.open("r") as fin:
        proof_retriever_conf_yaml = yaml.safe_load(fin)

    proof_retriever_raw_conf = proof_retriever_conf_from_yaml(proof_retriever_conf_yaml)
    proof_retriever_client_conf, next_num, server_commands = proof_conf_to_client_conf(
        proof_retriever_raw_conf, 0
    )

    if 0 < len(server_commands):
        start_servers(server_commands)
        wait_for_servers(next_num)

    worker_queue = mp.Queue()

    def proof_retriever_worker(
        proof_retriever_conf: ProofRetrieverConf,
        data_loc: Path,
        sentence_db_loc: Path,
    ):
        proof_retriever = proof_retriever_from_conf(proof_retriever_conf)
        sentence_db = SentenceDB.load(sentence_db_loc)
        _logger.info("Worker started.")
        while True:
            try:
                f_info = worker_queue.get(block=False)
                start = time.time()
                new_page_dict: dict[StepID, list[StepID]] = {}
                f_dp = f_info.get_dp(data_loc, sentence_db)
                for proof_idx, proof in enumerate(f_dp.proofs):
                    for step_idx, step in enumerate(proof.steps):
                        similar_steps = proof_retriever.get_similar_proof_steps(
                            step_idx, proof, f_dp
                        )
                        similar_step_ids = [sid for _, sid in similar_steps]
                        key_step_id = StepID.from_step_idx(step_idx, proof_idx, f_dp)
                        new_page_dict[key_step_id] = similar_step_ids
                new_page = ProofDBPage(new_page_dict)
                with open(save_loc / f_info.dp_name, "w") as f:
                    json.dump(new_page.to_json(), f, indent=2)
                end = time.time()
                _logger.info(f"Processed {f_info.dp_name} in {end - start} seconds.")
            except queue.Empty:
                sentence_db.close()
                close_proof_retriever(proof_retriever)
                return
            except Exception as e:
                _logger.error(f"WORKER ERROR: Error in worker: {e}")

    all_data_split_files = get_all_files(data_splits)
    worker_pool = ProcessPoolExecutor()

    for f_info in all_data_split_files:
        worker_queue.put(f_info)

    _logger.info(f"Using {num_workers} workers.")
    futures: list[Future] = []
    for _ in range(num_workers):
        worker_pool.submit(
            proof_retriever_worker,
            proof_retriever_client_conf,
            data_loc,
            sentence_db_loc,
        )

    _logger.info("Workers started.")
    for future in as_completed(futures):
        future.result()
