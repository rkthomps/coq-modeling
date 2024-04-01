from __future__ import annotations
from typing import Optional

import os
import math
import ipdb
import functools
import hashlib
import json
import argparse

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
from util.util import get_basic_logger

_logger = get_basic_logger(__name__) 

@functools.lru_cache(50)
def load_page(db_loc: str, page_idx: int, device: str) -> Optional[torch.Tensor]:
    page_loc = os.path.join(db_loc, f"{page_idx}.pt")
    if not os.path.exists(page_loc):
        return None
    #return torch.load(page_loc).to("cuda")
    return torch.load(page_loc).to(device)

class PremiseVectorDB:
    hash_cache: dict[str, str] = {}
    METADATA_LOC = "metadata.json"

    def __init__(
        self,
        db_loc: str,
        page_size: int,
        retriever_checkpoint_loc: str,
        sdb_hash: str,
    ):
        self.db_loc = db_loc
        self.page_size = page_size
        self.retriever_checkpoint_loc = retriever_checkpoint_loc
        self.sdb_hash = sdb_hash
        self.device = "cpu"
    
    def page_loc(self, idx: int) -> str:
        return os.path.join(self.db_loc, f"{idx}.pt")

    def group_idxs(self, idxs: list[int]) -> dict[int, list[int]]:
        page_idxs: dict[int, list[int]] = {}
        for idx in idxs:
            page_idx = idx // self.page_size
            if page_idx not in page_idxs:
                page_idxs[page_idx] = []
            page_idxs[page_idx].append(idx)
        return page_idxs

    def get_embs(self, idxs: list[int]) -> Optional[torch.Tensor]:
        page_groups = self.group_idxs(idxs)
        page_tensors: list[torch.Tensor] = []
        for pg_num, pg_idxs in page_groups.items():
            page_tensor = load_page(self.db_loc, pg_num, self.device)
            if page_tensor is None:
                return None
            #indices = (torch.tensor(pg_idxs, device="cuda") % self.page_size)
            indices = (torch.tensor(pg_idxs, device=self.device) % self.page_size)
            page_tensors.append((page_tensor[indices]))
        return torch.cat(page_tensors)


    # # MIGHT BE ABLE TO KEEP WHOLE MATRIX IN MEMORY. WILL HAVE TO SEE IF THAT's a GOOD IDEA
    def get(self, idx: int) -> Optional[torch.Tensor]: 
        page = idx // self.page_size 
        page_tensor = load_page(self.db_loc, page)
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
            "sdb_hash": self.sdb_hash,
            "retriever_checkpoint_loc": self.retriever_checkpoint_loc,
        }
        with open(metadata_loc, "w") as fout:
            fout.write(json.dumps(metadata))

    @classmethod
    def load(
        cls, db_loc: str,
    ) -> PremiseVectorDB:
        with open(os.path.join(db_loc, cls.METADATA_LOC)) as fin:
            metadata = json.load(fin)
        return cls(db_loc, metadata["page_size"], metadata["retriever_checkpoint_loc"], metadata["sdb_hash"])

    @classmethod
    def load_page_sentences(
        cls, page_num: int, page_size: int, sdb: SentenceDB, sdb_size: int
    ) -> list[DBSentence]:
        db_sentences: list[DBSentence] = []
        start = page_num * page_size
        end = min(sdb_size + 1, page_num * page_size + page_size)
        for i in range(start, end):
            if i == 0:
                db_sentences.append(DBSentence("Dummy sentence.", "", "[]", "TermType.LEMMA", 0)) # IDs start at 1
            else:
                db_sentences.append(sdb.retrieve(i))
        return db_sentences

    @classmethod
    def batch_sentences(
        cls, page_sentences: list[str], batch_size: int
    ) -> list[list[str]]:
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
    
    @classmethod
    def load_retriever(cls, checkpoint_loc: str) -> tuple[PremiseRetriever, GPT2Tokenizer, PremiseFormat, int]:
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


    @classmethod
    def create(
        cls,
        db_loc: str,
        page_size: int,
        batch_size: int,
        select_checkpoint: str,
        sentence_db_loc: str,
    ) -> PremiseVectorDB:
        retriever, tokenizer, premise_format, max_seq_len = cls.load_retriever(select_checkpoint)
        retriever.to("cuda")
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
            sentence_texts = [premise_format.format(Sentence.from_db_sentence(s)) for s in sentences_to_write]
            sentence_batches = cls.batch_sentences(sentence_texts, batch_size)
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
            page_loc = os.path.join(db_loc, f"{cur_page}.pt")
            torch.save(page_embs, page_loc)
            assert len(page_embs) == len(sentence_texts)
            num_written += len(sentence_texts)
            cur_page += 1
            _logger.info(f"Processed {num_written} out of {sdb_size}")
        return PremiseVectorDB(db_loc, page_size, select_checkpoint, sdb, sdb_hash)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("db_loc", help="Where to put the vector db.")
    parser.add_argument("page_size", type=int, help="Size of a page in the db.")
    parser.add_argument("batch_size", type=int, help="Batch size to use when making the db.")
    parser.add_argument(
        "select_checkpoint", help="Checkpoint to use for the select model."
    )
    parser.add_argument("sentence_db_loc", help="Location of the sentence database")


    args = parser.parse_args()

    pdb = PremiseVectorDB.create(
        args.db_loc,
        args.page_size,
        args.batch_size,
        args.select_checkpoint,
        args.sentence_db_loc,
    )
    pdb.save()
