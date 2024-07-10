from __future__ import annotations
from typing import Optional, Generator, Any
from dataclasses import dataclass
from pathlib import Path
import time
import argparse
import sys, os
import yaml
import pickle
import shutil
import multiprocessing


from proof_retrieval.proof_retriever import ProofDBQuery
from proof_retrieval.proof_idx import ProofIdx, ProofStateIdx
from proof_retrieval.proof_ret_model import ProofRetrievalModel
from util.vector_db_utils import get_embs, get, get_page_loc
from util.util import get_basic_logger

from data_management.sentence_db import SentenceDB
from data_management.dataset_file import Proof, DatasetFile
from data_management.splits import DataSplit, FileInfo, get_all_files

from util.constants import PROOF_VECTOR_DB_METADATA


import torch
from transformers import PreTrainedModel, PreTrainedTokenizer


_logger = get_basic_logger(__name__)


def step_iterator(
    data_split_locs: list[Path], data_loc: Path, sentence_db_loc: Path
) -> Generator[ProofDBQuery, None, None]:
    data_splits = [DataSplit.load(loc) for loc in data_split_locs]
    all_files = get_all_files(data_splits)
    sentence_db = SentenceDB.load(sentence_db_loc)
    for i, f_info in enumerate(all_files):
        if i % 100 == 0:
            _logger.info(f"Processing file {i}/{len(all_files)}")
        proofs = f_info.get_proofs(data_loc, sentence_db)
        for proof in proofs:
            for i, _ in enumerate(proof.steps):
                yield ProofDBQuery(i, proof, f_info.dp_name)


def page_iterator(
    step_gen: Generator[ProofDBQuery, None, None], page_size: int
) -> Generator[list[ProofDBQuery], None, None]:
    page: list[ProofDBQuery] = []
    for q in step_gen:
        page.append(q)
        if len(page) == page_size:
            yield page
            page = []
    if 0 < len(page):
        yield page


def batch_page(page: list[ProofDBQuery], batch_size: int) -> list[list[ProofDBQuery]]:
    return [page[i : i + batch_size] for i in range(0, len(page), batch_size)]


@dataclass
class ProofVectorDBConf:
    db_loc: Path
    page_size: int
    batch_size: int
    model_name: str | Path
    max_seq_len: int
    data_splits: list[Path]
    data_loc: Path
    sentence_db_loc: Path

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> ProofVectorDBConf:
        model_name = yaml_data["model_name"]
        if os.path.exists(model_name):
            model_name = Path(model_name)
        return cls(
            Path(yaml_data["db_loc"]),
            yaml_data["page_size"],
            yaml_data["batch_size"],
            model_name,
            yaml_data["max_seq_len"],
            [Path(p) for p in yaml_data["data_splits"]],
            Path(yaml_data["data_loc"]),
            Path(yaml_data["sentence_db_loc"]),
        )


class ProofVectorDB:
    def __init__(self, db_loc: Path, page_size: int, source: str, proof_idx: ProofIdx):
        self.db_loc = db_loc
        self.page_size = page_size
        self.source = source
        self.proof_idx = proof_idx
        self.device = "cpu"

    def save(self, path: Path):
        metadata = {
            "db_loc": str(self.db_loc),
            "page_size": self.page_size,
            "source": self.source,
            "proof_idx": self.proof_idx,
        }
        with (path / PROOF_VECTOR_DB_METADATA).open("wb") as fout:
            fout.write(pickle.dumps(metadata))

    def get_embs(self, idxs: list[int]) -> Optional[torch.Tensor]:
        return get_embs(idxs, self.page_size, self.db_loc, self.device)

    @classmethod
    def load(cls, db_loc: Path) -> ProofVectorDB:
        metadata_loc = db_loc / PROOF_VECTOR_DB_METADATA
        with metadata_loc.open("rb") as fin:
            metadata = pickle.load(fin)
        return cls(
            db_loc,
            metadata["page_size"],
            metadata["source"],
            metadata["proof_idx"],
        )

    @classmethod
    def create_proof_state_db(
        cls, conf: ProofVectorDBConf, process_id: int, num_processes: int
    ) -> ProofVectorDB:
        _logger.info("Loading model.")
        model = ProofRetrievalModel.load_model(conf.model_name, conf.max_seq_len)
        model.to(process_id)
        _logger.info(model.model.device)
        proof_indices: dict[int, int] = {}
        _logger.info("Creating proof state iterator.")
        step_gen = step_iterator(conf.data_splits, conf.data_loc, conf.sentence_db_loc)
        _logger.info("Creating page iterator.")
        _logger.info(f"Worker with process id {process_id} of {num_processes}")
        page_gen = page_iterator(step_gen, conf.page_size)
        for i, page in enumerate(page_gen):
            idxs = [
                ProofStateIdx.hash_proof_step(q.step_idx, q.proof, q.dp_name)
                for q in page
            ]
            for j, idx in enumerate(idxs):
                proof_indices[idx] = i * conf.page_size + j
            if i % num_processes != process_id:
                continue

            s = time.time()
            batches = batch_page(page, conf.batch_size)
            batch_encodings: list[torch.Tensor] = []
            for batch in batches:
                proof_states = [q.format() for q in batch]
                with torch.no_grad():
                    encodings = model.encode(proof_states)
                batch_encodings.append(encodings)
            page_loc = get_page_loc(conf.db_loc, i)
            page_encodings = torch.cat(batch_encodings, dim=0)
            # _logger.info(f"Encoding size {page_encodings.shape}")
            e = time.time()
            # _logger.info(f"Embedding time: {e - s}")
            s = time.time()
            torch.save(page_encodings, page_loc)
            e = time.time()
            # _logger.info(f"Saving time: {e - s}")
        return ProofVectorDB(
            conf.db_loc,
            conf.page_size,
            str(conf.model_name),
            ProofStateIdx(proof_indices),
        )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("conf_loc", help="Location of proof vector db config.")
    args = parser.parse_args(sys.argv[1:])

    conf_loc = Path(args.conf_loc)
    assert conf_loc.exists()

    with conf_loc.open("r") as fin:
        conf = yaml.safe_load(fin)

    proof_db_conf = ProofVectorDBConf.from_yaml(conf)
    if proof_db_conf.db_loc.exists():
        # yes_no = input(f"{proof_db_conf.db_loc} already exists. Overwrite? (y/n): ")
        # if yes_no != "y":
        raise FileExistsError(f"{proof_db_conf.db_loc}")
        # shutil.rmtree(proof_db_conf.db_loc)
    os.makedirs(proof_db_conf.db_loc)

    n_processes = torch.cuda.device_count()
    with multiprocessing.Pool(n_processes) as pool:
        results = pool.starmap(
            ProofVectorDB.create_proof_state_db,
            [(proof_db_conf, i, n_processes) for i in range(n_processes)],
        )

    results[0].save(proof_db_conf.db_loc)
