from __future__ import annotations
from typing import Any, Optional, Generator


import os
import json
import time
import random
import requests
from tqdm import tqdm
from pathlib import Path
from dataclasses import dataclass

from data_management.sentence_db import SentenceDB
from data_management.splits import FileInfo, DataSplit, Split, str2split, split2str

from model_deployment.prove import LocationInfo, RunProofConf
from model_deployment.searcher import SearcherConf, searcher_conf_from_yaml
from model_deployment.tactic_gen_client import (
    TacticGenConf,
    tactic_conf_update_ips,
    tactic_gen_client_from_conf,
    tactic_gen_conf_from_yaml,
    merge_tactic_confs,
)

from util.util import get_basic_logger, read_port_map, get_flexible_url

_logger = get_basic_logger(__name__)


PROOF_MAP_LOC = Path("./proof_maps")
QUEUE_LOC = "./queue"


@dataclass
class ProofMap:
    proofs: list[tuple[FileInfo, int]]

    def __len__(self) -> int:
        return len(self.proofs)

    def get(self, idx: int) -> tuple[FileInfo, int]:
        return self.proofs[idx]

    def to_json(self):
        objs: list[dict[str, str | int]] = []
        for f_info, proof_idx in self.proofs:
            objs.append({"file_info": f_info.to_json(), "proof_idx": proof_idx})
        return {"map": objs}

    def save(self, path: Path):
        with path.open("w") as fout:
            fout.write(json.dumps(self.to_json(), indent=2))

    @classmethod
    def from_json(cls, json_data: Any) -> ProofMap:
        proofs: list[tuple[FileInfo, int]] = []
        for obj in json_data["map"]:
            proofs.append((FileInfo.from_json(obj["file_info"]), obj["proof_idx"]))
        return cls(proofs)

    @classmethod
    def load(cls, path: Path) -> ProofMap:
        with path.open("r") as fin:
            return cls.from_json(json.load(fin))

    @classmethod
    def create(
        cls,
        data_split: DataSplit,
        split: Split,
        data_loc: Path,
        sentence_db: SentenceDB,
    ) -> ProofMap:
        proofs: list[tuple[FileInfo, int]] = []
        for f in tqdm(data_split.get_file_list(split)):
            f_proofs = f.get_proofs(data_loc, sentence_db)
            for i, f_proof in enumerate(f_proofs):
                if not f_proof.is_proof_independent():
                    continue
                proofs.append((f, i))
        random.seed(0)
        random.shuffle(proofs)
        return cls(proofs)


@dataclass
class EvalConf:
    n_procs: int
    split: Split
    save_loc: Path
    data_loc: Path
    sentence_db_loc: Path
    data_split_loc: Path
    search_conf: SearcherConf
    tactic_conf: TacticGenConf
    max_eval_proofs: Optional[int]

    def update_ips(self, port_map: dict[int, tuple[str, int]]):
        tactic_conf_update_ips(self.tactic_conf, port_map)

    def get_proof_confs(self) -> Generator[EvalProofConf, None, None]:
        data_split = DataSplit.load(self.data_split_loc)
        sentence_db = SentenceDB.load(self.sentence_db_loc)
        file_list = data_split.get_file_list(self.split)
        if self.max_eval_proofs is not None and self.max_eval_proofs < len(file_list):
            random.seed(0)
            file_list = random.sample(file_list, self.max_eval_proofs)
        for file_info in file_list:
            proofs = file_info.get_proofs(self.data_loc, sentence_db)
            for i, proof in enumerate(proofs):
                if not proof.is_proof_independent():
                    _logger.debug(f"Skipping {proof.theorem.term.text}")
                    continue
                yield EvalProofConf(
                    file_info,
                    i,
                    self.split,
                    self.data_loc,
                    self.sentence_db_loc,
                    self.data_split_loc,
                    self.search_conf,
                    self.tactic_conf,
                )

    def merge(self, other: EvalConf) -> EvalConf:
        assert self.n_procs == other.n_procs
        assert self.split == other.split
        assert self.save_loc == other.save_loc
        assert self.data_loc == other.data_loc
        assert self.sentence_db_loc == other.sentence_db_loc
        assert self.data_split_loc == other.data_split_loc
        assert self.search_conf == other.search_conf
        assert self.max_eval_proofs == other.max_eval_proofs
        new_tactic_conf = merge_tactic_confs(self.tactic_conf, other.tactic_conf)
        return EvalConf(
            self.n_procs,
            self.split,
            self.save_loc,
            self.data_loc,
            self.sentence_db_loc,
            self.data_split_loc,
            self.search_conf,
            new_tactic_conf,
            self.max_eval_proofs,
        )

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> EvalConf:
        max_eval_proofs = None
        if "max_eval_proofs" in yaml_data:
            max_eval_proofs = yaml_data["max_eval_proofs"]
        return cls(
            yaml_data["n_procs"],
            str2split(yaml_data["split"]),
            Path(yaml_data["save_loc"]),
            Path(yaml_data["data_loc"]),
            Path(yaml_data["sentence_db_loc"]),
            Path(yaml_data["data_split_loc"]),
            searcher_conf_from_yaml(yaml_data["search"]),
            tactic_gen_conf_from_yaml(yaml_data["tactic_gen"]),
            max_eval_proofs,
        )


@dataclass
class EvalProofConf:
    file_info: FileInfo
    proof_idx: int
    split: Split
    data_loc: Path
    sentence_db_loc: Path
    data_split_loc: Path
    search_conf: SearcherConf
    tactic_conf: TacticGenConf

    def to_run_conf(self) -> RunProofConf:
        sentence_db = SentenceDB.load(self.sentence_db_loc)
        dp_obj = self.file_info.get_dp(self.data_loc, sentence_db)
        data_split = DataSplit.load(self.data_split_loc)
        location_info = LocationInfo(
            self.data_loc,
            self.file_info,
            self.split,
            dp_obj,
            self.proof_idx,
            sentence_db,
            data_split,
        )
        tactic_client = tactic_gen_client_from_conf(self.tactic_conf)
        return RunProofConf(
            location_info, self.search_conf, tactic_client, False, False
        )


def create_eval_proof_map(eval_conf: EvalConf) -> ProofMap:
    if eval_conf.split == Split.TRAIN:
        raise ValueError("Evaluation on training set not supported.")

    os.makedirs(PROOF_MAP_LOC, exist_ok=True)
    proof_map_loc = PROOF_MAP_LOC / split2str(eval_conf.split)
    if proof_map_loc.exists():
        print(f"Using proof map located at {proof_map_loc}")
        return ProofMap.load(proof_map_loc)

    _logger.info(f"Creating proof map.")
    data_split = DataSplit.load(eval_conf.data_split_loc)
    sentence_db = SentenceDB.load(eval_conf.sentence_db_loc)
    proof_map = ProofMap.create(
        data_split, eval_conf.split, eval_conf.data_loc, sentence_db
    )
    proof_map.save(proof_map_loc)
    return proof_map


def wait_for_servers(next_server_num: int) -> dict[int, tuple[str, int]]:
    """Returns a map of port -> ip addr"""
    session = requests.Session()
    urls: list[str] = []

    cur_port_map = read_port_map()
    while len(cur_port_map) < next_server_num:
        _logger.info(f"Port map of length {len(cur_port_map)} not complete. Sleeping.")
        time.sleep(1)
        cur_port_map = read_port_map()

    for port_incr in range(next_server_num):
        ip_addr, port = cur_port_map[port_incr]
        url = get_flexible_url(port_incr, ip_addr, port).get_url()
        urls.append(url)

    _logger.info("Waiting for urls: " + str(urls))
    for server_url in urls:
        while True:
            try:
                session.get(server_url)
                break
            except requests.exceptions.RequestException:
                continue
    return cur_port_map