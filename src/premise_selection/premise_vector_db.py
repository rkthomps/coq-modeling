from __future__ import annotations
from typing import Optional, Callable

import os
import math
from pathlib import Path
import ipdb
import functools
import hashlib
import json
import argparse
import logging
import shutil

import torch
from transformers import GPT2Tokenizer
from yaml import load, Loader

from data_management.dataset_file import Sentence
from data_management.sentence_db import SentenceDB, DBSentence
from premise_selection.model import PremiseRetriever
from premise_selection.select_data import tokenize_strings
from premise_selection.premise_formatter import PremiseFormat, PREMISE_ALIASES
from util.train_utils import get_required_arg
from util.constants import PREMISE_DATA_CONF_NAME, TRAINING_CONF_NAME, TMP_LOC
from util.vector_db_utils import get_embs, get, get_page_loc

from util.util import get_basic_logger


_logger = get_basic_logger(__name__)


class VectorDB:
    hash_cache: dict[Path, str] = {}
    METADATA_LOC = "metadata.json"

    def __init__(
        self,
        db_loc: Path,
        page_size: int,
        source: str,
        sdb_hash: str,
    ):
        self.db_loc = db_loc
        self.page_size = page_size
        self.source = source  # Just for book keeping
        self.sdb_hash = sdb_hash
        self.device = "cpu"

    def get_embs(self, idxs: list[int]) -> Optional[torch.Tensor]:
        return get_embs(idxs, self.page_size, self.db_loc, self.device)

    def get(self, idx: int) -> Optional[torch.Tensor]:
        return get(idx, self.page_size, self.db_loc, self.device)

    @classmethod
    def __hash_sdb(cls, sentence_db_loc: Path) -> str:
        if sentence_db_loc in cls.hash_cache:
            return cls.hash_cache[sentence_db_loc]
        with open(sentence_db_loc, "rb") as fin:
            c = fin.read()
        m = hashlib.sha256()
        m.update(c)
        hash = m.hexdigest()
        cls.hash_cache[sentence_db_loc] = hash
        return hash

    def save(self):
        metadata_loc = os.path.join(self.db_loc, self.METADATA_LOC)
        metadata = {
            "page_size": self.page_size,
            "source": self.source,
            "sdb_hash": self.sdb_hash,
        }
        with open(metadata_loc, "w") as fout:
            fout.write(json.dumps(metadata))

    @classmethod
    def load(
        cls,
        db_loc: Path,
    ) -> VectorDB:
        with open(os.path.join(db_loc, cls.METADATA_LOC)) as fin:
            metadata = json.load(fin)
        tmp_path = TMP_LOC / db_loc.name
        if tmp_path.exists():
            _logger.info(f"Using vector db {tmp_path}")
            use_path = tmp_path
        else:
            use_path = db_loc

        return cls(
            use_path,
            metadata["page_size"],
            metadata["source"],
            metadata["sdb_hash"],
        )

    @classmethod
    def load_page_sentences(
        cls, page_num: int, page_size: int, sdb: SentenceDB, sdb_size: int
    ) -> list[DBSentence]:
        db_sentences: list[DBSentence] = []
        start = page_num * page_size
        end = min(sdb_size + 1, page_num * page_size + page_size)
        for i in range(start, end):
            if i == 0:
                db_sentences.append(
                    DBSentence("Dummy sentence.", "", "[]", "TermType.LEMMA", 0)
                )  # IDs start at 1
            else:
                db_sentences.append(sdb.retrieve(i))
        return db_sentences

    @classmethod
    def create_premise_db(
        cls,
        db_loc: Path,
        page_size: int,
        source: str,  # Describes the source of the database
        encoder: Callable[[list[DBSentence]], torch.Tensor],
        sentence_db_loc: Path,
    ) -> VectorDB:
        sdb = SentenceDB.load(sentence_db_loc)
        sdb_hash = cls.__hash_sdb(sentence_db_loc)
        sdb_size = sdb.size()
        num_written = 0
        cur_page = 0
        if os.path.exists(db_loc):
            raise FileExistsError(f"{db_loc}")
        os.makedirs(db_loc)
        while num_written < sdb_size + 1:
            sentences_to_write = cls.load_page_sentences(
                cur_page, page_size, sdb, sdb_size
            )
            page_embs = encoder(sentences_to_write)
            assert len(page_embs) == len(sentences_to_write)
            page_loc = get_page_loc(db_loc, cur_page) 
            torch.save(page_embs, page_loc)
            num_written += len(sentences_to_write)
            cur_page += 1
            _logger.info(f"Processed {num_written} out of {sdb_size}")
        return VectorDB(db_loc, page_size, source, sdb_hash)

    @classmethod
    def create_proof_db(
        cls,
        db_loc: Path,
        page_size: int,
        source: str,
        encoder: Callable[[list[str]], torch.Tensor],
    ) -> VectorDB:
        raise NotImplementedError


def batch_sentences(page_sentences: list[str], batch_size: int) -> list[list[str]]:
    batches: list[list[str]] = []
    cur_batch: list[str] = []
    for s in page_sentences:
        cur_batch.append(s)
        if len(cur_batch) % batch_size == 0:
            batches.append(cur_batch)
            cur_batch = []
    if 0 < len(cur_batch):
        batches.append(cur_batch)
    return batches


def load_retriever(
    checkpoint_loc: Path,
) -> tuple[PremiseRetriever, GPT2Tokenizer, type[PremiseFormat], int]:
    data_preparation_conf = checkpoint_loc.parent / PREMISE_DATA_CONF_NAME
    with open(data_preparation_conf, "r") as fin:
        premise_conf = load(fin, Loader=Loader)
    model_conf_loc = checkpoint_loc.parent / TRAINING_CONF_NAME
    with open(model_conf_loc, "r") as fin:
        model_conf = load(fin, Loader=Loader)
    max_seq_len = get_required_arg("max_seq_len", model_conf)
    tokenizer = GPT2Tokenizer.from_pretrained(model_conf["model_name"])
    premise_format_alias = premise_conf["premise_format_type_alias"]
    premise_format = PREMISE_ALIASES[premise_format_alias]
    retriever = PremiseRetriever.from_pretrained(checkpoint_loc)
    return retriever, tokenizer, premise_format, max_seq_len


def select_encode(
    retriever: PremiseRetriever,
    tokenizer: GPT2Tokenizer,
    premise_format: type[PremiseFormat],
    max_seq_len: int,
    batch_size: int,
    ss: list[DBSentence],
) -> torch.Tensor:
    sentence_texts = [premise_format.format(Sentence.from_db_sentence(s)) for s in ss]
    sentence_batches = batch_sentences(sentence_texts, batch_size)
    batch_embs: list[torch.Tensor] = []
    for batch in sentence_batches:
        with torch.no_grad():
            batch_inputs = tokenize_strings(
                tokenizer,
                batch,
                max_seq_len,
            )
            batch_emb = retriever.encode_premise(
                batch_inputs.input_ids, batch_inputs.attention_mask
            )
        batch_embs.append(batch_emb)
    page_embs = torch.cat(batch_embs).to("cpu")
    return page_embs


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--db_loc", help="Where to put the vector db.")
    parser.add_argument("--page_size", type=int, help="Size of a page in the db.")
    parser.add_argument(
        "--batch_size", type=int, help="Batch size to use when making the db."
    )
    parser.add_argument(
        "--select_checkpoint", help="Checkpoint to use for the select model."
    )
    parser.add_argument("--sentence_db_loc", help="Location of the sentence database")
    args = parser.parse_args()

    db_loc = Path(args.db_loc)
    page_size = args.page_size
    batch_size = args.batch_size
    checkpoint_loc = Path(args.select_checkpoint)
    sentence_db_loc = Path(args.sentence_db_loc)

    if db_loc.exists():
        raise FileExistsError(f"{db_loc}")

    assert checkpoint_loc.exists()
    assert sentence_db_loc.exists()

    retriever, tokenizer, premise_format, max_seq_len = load_retriever(checkpoint_loc)
    retriever.to("cuda")
    encode_fn = functools.partial(
        select_encode,
        retriever,
        tokenizer,
        premise_format,
        max_seq_len,
        batch_size,
    )

    pdb = VectorDB.create_premise_db(
        Path(db_loc),
        page_size,
        str(checkpoint_loc),
        encode_fn,
        sentence_db_loc,
    )
    pdb.save()
