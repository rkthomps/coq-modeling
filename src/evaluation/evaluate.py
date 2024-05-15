from __future__ import annotations
import os
import sys
import traceback
import csv
import ipdb
import random
from typing import Any, Generator, Optional
from pathlib import Path
from dataclasses import dataclass
from threading import Thread
import multiprocessing as mp
from multiprocessing import context
from multiprocessing.pool import AsyncResult
import pickle

from data_management.sentence_db import SentenceDB
from data_management.splits import Split, DataSplit, FileInfo, split2str, str2split
from model_deployment.prove import (
    MCTSSummary,
    SearchSummary,
    summary_from_result,
    run_proof,
    RunProofConf,
    LocationInfo,
)
from model_deployment.mcts_searcher import MCTSConf
from model_deployment.classical_searcher import ClassicalSearchConf
from model_deployment.searcher import (
    SearcherConf,
    Searcher,
    SuccessfulSearch,
    FailedSearch,
    searcher_conf_from_yaml,
)
from model_deployment.tactic_gen_client import (
    TacticGenConf,
    tactic_gen_conf_from_yaml,
    tactic_gen_client_from_conf,
    tactic_conf_update_ips,
    merge_tactic_confs,
)
from util.constants import CLEAN_CONFIG
from util.util import get_basic_logger

_logger = get_basic_logger(__name__)


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

    def update_ips(self, port_map: dict[int, str]):
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
                try:
                    proof.get_theorem_name()
                except ValueError:
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


def eval_proof(eval_conf: EvalProofConf, save_dir: Path):
    run_conf = eval_conf.to_run_conf()
    result = run_proof(run_conf)
    file = eval_conf.data_loc / eval_conf.file_info.file
    theorem_name = (
        run_conf.location_info.dataset_file.proofs[
            run_conf.location_info.dp_proof_idx
        ].get_theorem_name()
        + "-"
        + str(run_conf.location_info.dp_proof_idx)
    )
    summary = summary_from_result(file, theorem_name, result)
    summary.pretty_print()
    summary.save(save_dir)


def load_results(save_dir: Path) -> list[SearchSummary]:
    summaries: list[SearchSummary] = []
    for f in os.listdir(save_dir):
        with (save_dir / f).open("rb") as fin:
            summary = pickle.load(fin)
            summaries.append(summary)
    return summaries


if __name__ == "__main__":
    conf_loc = Path(f"./{CLEAN_CONFIG}")
    with conf_loc.open("rb") as fin:
        conf: EvalConf = pickle.load(fin)
        assert "EvalConf" in str(conf.__class__)  # isinstance didn't work

    assert not conf.save_loc.exists()
    os.makedirs(conf.save_loc)

    process_results: list[AsyncResult] = []
    print("Getting individual proof confs...")
    eval_proofs = list(conf.get_proof_confs())
    random.seed(0)
    random.shuffle(eval_proofs)
    if conf.max_eval_proofs is not None:
        eval_proofs = eval_proofs[: conf.max_eval_proofs]

    print("Running Evaluation...")
    with mp.Pool(conf.n_procs) as pool:
        for eval_proof_conf in eval_proofs:
            res = pool.apply_async(eval_proof, (eval_proof_conf, conf.save_loc))
            process_results.append(res)

        for r, eval_proof_conf in zip(process_results, eval_proofs):
            try:
                r.get(2 * conf.search_conf.timeout)
            except Exception as e:
                print(traceback.format_exc())
                # _logger.warning(f"Got exception: {e}")
                run_conf = eval_proof_conf.to_run_conf()
                file = eval_proof_conf.data_loc / eval_proof_conf.file_info.file
                theorem_name = (
                    run_conf.location_info.dataset_file.proofs[
                        run_conf.location_info.dp_proof_idx
                    ].get_theorem_name()
                    + "-"
                    + str(run_conf.location_info.dp_proof_idx)
                )
                match conf.search_conf:
                    case MCTSConf():
                        summary = MCTSSummary.from_search_result(
                            file, theorem_name, None
                        )
                    case ClassicalSearchConf():
                        summary = SearchSummary.from_search_result(
                            file, theorem_name, None
                        )
                summary.pretty_print()
                summary.save(conf.save_loc)

    results = load_results(conf.save_loc)
    results.sort()
    if 0 == len(results):
        print("Nothing to write.", file=sys.stderr)

    with (conf.save_loc / "results.csv").open("w", newline="") as fout:
        field_names, _ = results[0].to_csv_dict()
        writer = csv.DictWriter(fout, field_names)
        writer.writeheader()
        for r in results:
            _, r_dict = r.to_csv_dict()
            writer.writerow(r_dict)
