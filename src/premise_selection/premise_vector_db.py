from __future__ import annotations
from typing import Optional, Callable

import os
import math
import ipdb
import functools
import hashlib
import json
import argparse
import logging

import torch
from transformers import GPT2Tokenizer
from yaml import load, Loader

from data_management.dataset_file import Sentence
from data_management.sentence_db import SentenceDB, DBSentence
from premise_selection.model import PremiseRetriever
from premise_selection.datamodule import tokenize_strings
from premise_selection.premise_formatter import PremiseFormat, PREMISE_ALIASES
from util.train_utils import get_required_arg
from util.constants import PREMISE_DATA_CONF_NAME, TRAINING_CONF_NAME


@functools.lru_cache(50)
def load_page(db_loc: str, page_idx: int, device: str) -> Optional[torch.Tensor]:
    page_loc = os.path.join(db_loc, f"{page_idx}.pt")
    if not os.path.exists(page_loc):
        return None
    # return torch.load(page_loc).to("cuda")
    return torch.load(page_loc).to(device)


class PremiseVectorDB:
    hash_cache: dict[str, str] = {}
    METADATA_LOC = "metadata.json"

    def __init__(
        self,
        db_loc: str,
        page_size: int,
        source: str,
        sdb_hash: str,
    ):
        self.db_loc = db_loc
        self.page_size = page_size
        self.source = source  # Just for book keeping
        self.sdb_hash = sdb_hash
        self.device = "cpu"

    def page_loc(self, idx: int) -> str:
        return os.path.join(self.db_loc, f"{idx}.pt")

    def group_idxs(self, idxs: list[int]) -> dict[int, list[tuple[int, int]]]:
        page_idxs: dict[int, list[tuple[int, int]]] = {}
        for i, idx in enumerate(idxs):
            page_idx = idx // self.page_size
            if page_idx not in page_idxs:
                page_idxs[page_idx] = []
            page_idxs[page_idx].append((idx, i))  # vector idx, orig idx
        return page_idxs

    def get_embs(self, idxs: list[int]) -> Optional[torch.Tensor]:
        page_groups = self.group_idxs(idxs)
        page_tensors: list[torch.Tensor] = []
        all_orig_idxs: list[int] = []
        for pg_num, pg_idxs in page_groups.items():
            page_idxs = [p for p, _ in pg_idxs]
            orig_idxs = [o for _, o in pg_idxs]
            all_orig_idxs.extend(orig_idxs)
            page_tensor = load_page(self.db_loc, pg_num, self.device)
            if page_tensor is None:
                return None
            indices = torch.tensor(page_idxs, device=self.device) % self.page_size
            page_tensors.append((page_tensor[indices]))
        reidx = sorted(range(len(all_orig_idxs)), key=lambda idx: all_orig_idxs[idx])
        reidx_tensor = torch.tensor(reidx, device=self.device)
        big_tensor = torch.cat(page_tensors)
        return big_tensor[reidx_tensor]

    def get(self, idx: int) -> Optional[torch.Tensor]:
        page = idx // self.page_size
        page_tensor = load_page(self.db_loc, page, self.device)
        if page_tensor is not None:
            return page_tensor[idx % self.page_size]
        return None

    @classmethod
    def __hash_sdb(cls, sentence_db_loc: str) -> str:
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
        db_loc: str,
    ) -> PremiseVectorDB:
        with open(os.path.join(db_loc, cls.METADATA_LOC)) as fin:
            metadata = json.load(fin)
        return cls(
            db_loc,
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
    def create(
        cls,
        db_loc: str,
        page_size: int,
        source: str,  # Describes the source of the database
        encoder: Callable[[list[DBSentence]], torch.Tensor],
        sentence_db_loc: str,
    ) -> PremiseVectorDB:
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
            page_loc = os.path.join(db_loc, f"{cur_page}.pt")
            torch.save(page_embs, page_loc)
            num_written += len(sentences_to_write)
            cur_page += 1
            print(f"Processed {num_written} out of {sdb_size}")
        return PremiseVectorDB(db_loc, page_size, source, sdb_hash)


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
    checkpoint_loc: str,
) -> tuple[PremiseRetriever, GPT2Tokenizer, type[PremiseFormat], int]:
    model_loc = os.path.dirname(checkpoint_loc)
    data_preparation_conf = os.path.join(model_loc, PREMISE_DATA_CONF_NAME)
    with open(data_preparation_conf, "r") as fin:
        premise_conf = load(fin, Loader=Loader)
    model_conf_loc = os.path.join(model_loc, TRAINING_CONF_NAME)
    with open(model_conf_loc, "r") as fin:
        model_conf = load(fin, Loader=Loader)
    max_seq_len = get_required_arg("max_seq_len", model_conf)
    tokenizer = GPT2Tokenizer.from_pretrained(model_conf["model_name"])
    premise_format_alias = premise_conf["premise_format_alias"]
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
    parser.add_argument("db_loc", help="Where to put the vector db.")
    parser.add_argument("page_size", type=int, help="Size of a page in the db.")
    parser.add_argument(
        "batch_size", type=int, help="Batch size to use when making the db."
    )
    parser.add_argument(
        "select_checkpoint", help="Checkpoint to use for the select model."
    )
    parser.add_argument("sentence_db_loc", help="Location of the sentence database")

    args = parser.parse_args()

    retriever, tokenizer, premise_format, max_seq_len = load_retriever(
        args.select_checkpoint
    )
    retriever.to("cuda")
    encode_fn = functools.partial(
        select_encode,
        retriever,
        tokenizer,
        premise_format,
        max_seq_len,
        args.batch_size,
    )

    pdb = PremiseVectorDB.create(
        args.db_loc,
        args.page_size,
        args.select_checkpoint,
        encode_fn,
        args.sentence_db_loc,
    )
    pdb.save()
