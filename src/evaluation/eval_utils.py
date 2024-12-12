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
)

from coqstoq import Split, get_theorem_list
from coqstoq.eval_thms import EvalTheorem

from util.file_queue import FileQueue
from util.util import get_basic_logger, read_port_map, get_flexible_url
from util.constants import TMP_LOC, SYNTH_DATA_LOC
from util.coqstoq_utils import split2str, str2split

_logger = get_basic_logger(__name__)


QUEUE_LOC = TMP_LOC / "queue"


def initialize_and_fill_queue(
    queue_loc: Path,
    conf: EvalConf,
):
    theorem_list = get_theorem_list(conf.split, conf.coqstoq_loc)
    q = FileQueue[EvalTheorem](queue_loc)
    q.initialize()

    if conf.proof_ids is not None:
        for id in conf.proof_ids:
            q.put(theorem_list[id])
    else:
        q.put_all(theorem_list)


@dataclass
class EvalConf:
    split: Split
    save_loc: Path
    data_loc: Path
    coqstoq_loc: Path
    sentence_db_loc: Path
    search_conf: SearcherConf
    tactic_confs: list[TacticGenConf]
    proof_ids: Optional[list[int]]
    rerun_errors: bool

    def update_ips(self, port_map: dict[int, tuple[str, int]]):
        for conf in self.tactic_confs:
            tactic_conf_update_ips(conf, port_map)

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> EvalConf:
        proof_ids = yaml_data.get("proof_ids", None)
        rerun_errors = yaml_data.get("rerun_errors", False)
        if "tactic_gens" in yaml_data:
            tactic_gens = [
                tactic_gen_conf_from_yaml(tactic_gen)
                for tactic_gen in yaml_data["tactic_gens"]
            ]
        elif "tactic_gen" in yaml_data:
            tactic_gens = [tactic_gen_conf_from_yaml(yaml_data["tactic_gen"])]
        else:
            raise ValueError("No tactic gen conf found.")

        return cls(
            str2split(yaml_data["split"]),
            Path(yaml_data["save_loc"]),
            Path(yaml_data["data_loc"]),
            Path(yaml_data["coqstoq_loc"]),
            Path(yaml_data["sentence_db_loc"]),
            searcher_conf_from_yaml(yaml_data["search"]),
            tactic_gens,
            proof_ids,
            rerun_errors,
        )


# TODO: Have not adjusted the premise evaluation to work with coqstoq.
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
