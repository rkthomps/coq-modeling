from __future__ import annotations
from typing import Any, Optional, Generator


import os
import json
import time
import pickle
import random
import requests
from tqdm import tqdm
from pathlib import Path
from dataclasses import dataclass
from hashlib import sha256

from data_management.sentence_db import SentenceDB
from data_management.splits import FileInfo, DataSplit, Split, str2split, split2str

from model_deployment.prove import LocationInfo, RunProofConf
from model_deployment.searcher import SearcherConf, searcher_conf_from_yaml
from premise_selection.rerank_client import (
    PremiseClient,
    PremiseConf,
    premise_conf_from_yaml,
)
from model_deployment.tactic_gen_client import (
    TacticGenConf,
    tactic_conf_update_ips,
    tactic_gen_client_from_conf,
    tactic_gen_conf_from_yaml,
    merge_tactic_confs,
)

from util.file_queue import FileQueue
from util.util import get_basic_logger, read_port_map, get_flexible_url
from util.constants import TMP_LOC, SYNTH_DATA_LOC

_logger = get_basic_logger(__name__)


PROOF_MAP_LOC = SYNTH_DATA_LOC / "proof_maps"
QUEUE_LOC = TMP_LOC / "queue"


def get_save_name(f_info: FileInfo, proof_idx: int) -> str:
    return f"{f_info.dp_name}-{proof_idx}.json"


def initialize_and_fill_queue(
    queue_loc: Path,
    conf: EvalConf | PremiseEvalConf,
):
    proof_map = create_eval_proof_map(
        conf.split, conf.data_split_loc, conf.sentence_db_loc, conf.data_loc
    )
    q = FileQueue(queue_loc)
    q.initialize()
    if conf.end_at is not None and conf.start_at is not None:
        q.put_all(proof_map.proofs[conf.start_at : conf.end_at])
    elif conf.end_at is not None:
        q.put_all(proof_map.proofs[: conf.end_at])
    elif conf.start_at is not None:
        q.put_all(proof_map.proofs[conf.start_at :])
    else:
        q.put_all(proof_map.proofs)


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
    start_at: Optional[int]
    end_at: Optional[int]

    def update_ips(self, port_map: dict[int, tuple[str, int]]):
        tactic_conf_update_ips(self.tactic_conf, port_map)

    def get_proof_confs(self) -> Generator[EvalProofConf, None, None]:
        data_split = DataSplit.load(self.data_split_loc)
        sentence_db = SentenceDB.load(self.sentence_db_loc)
        file_list = data_split.get_file_list(self.split)
        if self.end_at is not None and self.end_at < len(file_list):
            random.seed(0)
            file_list = random.sample(file_list, self.end_at)
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
        assert self.end_at == other.end_at
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
            self.start_at,
            self.end_at,
        )

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> EvalConf:
        end_at = None
        if "end_at" in yaml_data:
            end_at = yaml_data["end_at"]
        start_at = None
        if "start_at" in yaml_data:
            start_at = yaml_data["start_at"]

        return cls(
            yaml_data["n_procs"],
            str2split(yaml_data["split"]),
            Path(yaml_data["save_loc"]),
            Path(yaml_data["data_loc"]),
            Path(yaml_data["sentence_db_loc"]),
            Path(yaml_data["data_split_loc"]),
            searcher_conf_from_yaml(yaml_data["search"]),
            tactic_gen_conf_from_yaml(yaml_data["tactic_gen"]),
            start_at,
            end_at,
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


@dataclass
class PremiseStepResult:
    step_idx: int
    num_premises: int
    hits_on: list[int]


@dataclass
class PremiseProofResult:
    file: str
    proof_idx: int
    step_results: list[PremiseStepResult]

    def save(self, path: Path):
        save_file_name = str(self.file).replace("/", "-")
        save_name = f"{save_file_name}-{self.proof_idx}.pkl"
        _logger.info(f"Saving to {path / save_name}.")
        with (path / save_name).open("wb") as fout:
            pickle.dump(self, fout)


@dataclass
class PremiseEvalConf:
    split: Split
    save_loc: Path
    data_loc: Path
    sentence_db_loc: Path
    data_split_loc: Path
    premise_conf: PremiseConf
    start_at: Optional[int]
    end_at: Optional[int]

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> PremiseEvalConf:
        end_at = None
        if "end_at" in yaml_data:
            end_at = yaml_data["end_at"]
        start_at = None
        if "start_at" in yaml_data:
            start_at = yaml_data["start_at"]
        return cls(
            str2split(yaml_data["split"]),
            Path(yaml_data["save_loc"]),
            Path(yaml_data["data_loc"]),
            Path(yaml_data["sentence_db_loc"]),
            Path(yaml_data["data_split_loc"]),
            premise_conf_from_yaml(yaml_data["premise"]),
            start_at,
            end_at,
        )


def __get_data_split_hash(data_split_loc: Path) -> str:
    with data_split_loc.open("r") as fin:
        m = sha256()
        m.update(str.encode(fin.read()))
        encoding = m.hexdigest()
    return encoding


def create_eval_proof_map(
    split: Split, data_split_loc: Path, sentence_db_loc: Path, data_loc: Path
) -> ProofMap:
    if split == Split.TRAIN:
        raise ValueError("Evaluation on training set not supported.")

    os.makedirs(PROOF_MAP_LOC, exist_ok=True)
    split_encoding = __get_data_split_hash(data_split_loc)
    proof_map_loc = PROOF_MAP_LOC / f"{split_encoding}-{split2str(split)}"
    if proof_map_loc.exists():
        print(f"Using proof map located at {proof_map_loc}")
        return ProofMap.load(proof_map_loc)

    _logger.info(f"Creating proof map.")
    data_split = DataSplit.load(data_split_loc)
    sentence_db = SentenceDB.load(sentence_db_loc)
    proof_map = ProofMap.create(data_split, split, data_loc, sentence_db)
    proof_map.save(proof_map_loc)
    return proof_map


def wait_for_servers(next_server_num: int) -> dict[int, tuple[str, int]]:
    """Returns a map of port -> ip addr"""
    session = requests.Session()
    urls: list[str] = []

    cur_port_map = read_port_map()
    total_time_slept = 0
    while len(cur_port_map) < next_server_num:
        if 1 < total_time_slept and total_time_slept % 10 == 0:
            _logger.info(
                f"Port map of length {len(cur_port_map)} not complete after {total_time_slept}."
            )
        time.sleep(1)
        total_time_slept += 1
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
