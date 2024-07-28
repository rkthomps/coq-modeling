import sys, os
import argparse
import json
import pickle
import time
from pathlib import Path
import subprocess
import multiprocessing as mp

from data_management.splits import DataSplit, FileInfo
from data_management.sentence_db import SentenceDB
from evaluation.eval_utils import ProofMap, EvalConf

from model_deployment.mcts_searcher import MCTSConf
from model_deployment.classical_searcher import ClassicalSearchConf
from model_deployment.straight_line_searcher import StraightLineSearcherConf
from model_deployment.prove import (
    LocationInfo,
    RunProofConf,
    run_proof,
    summary_from_result,
    save_summary,
    get_save_loc,
    summary_from_json,
    pretty_print_summary,
    ClassicalSummary,
    MCTSSummary,
    StraightLineSummary,
    Summary,
)
from model_deployment.tactic_gen_client import tactic_gen_client_from_conf
from util.constants import CLEAN_CONFIG
from util.util import get_basic_logger
from util.file_queue import FileQueue, EmptyFileQueueError

_logger = get_basic_logger(__name__)


def get_orig_summary(
    file: Path, theorem: str, proof_idx: int, theorem_id: str, eval_conf: EvalConf
) -> Summary:
    match eval_conf.search_conf:
        case MCTSConf():
            return MCTSSummary.from_search_result(
                file, theorem, proof_idx, theorem_id, None
            )
        case ClassicalSearchConf():
            return ClassicalSummary.from_search_result(
                file, theorem, proof_idx, theorem_id, None
            )
        case StraightLineSearcherConf():
            return StraightLineSummary.from_search_result(
                file, theorem, proof_idx, theorem_id, None
            )


def run_and_save_proof(run_conf: RunProofConf):
    result = run_proof(run_conf)
    summary = summary_from_result(
        run_conf.file,
        run_conf.theorem,
        run_conf.loc.dp_proof_idx,
        run_conf.theorem_id,
        result,
    )
    _logger.info(pretty_print_summary(summary))
    save_summary(summary, eval_conf.save_loc)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("eval_pkl_conf_loc")
    parser.add_argument("queue_loc")

    args = parser.parse_args(sys.argv[1:])
    eval_pkl_conf_loc = Path(args.eval_pkl_conf_loc)
    queue_loc = Path(args.queue_loc)
    assert eval_pkl_conf_loc.exists()
    assert queue_loc.exists()

    with eval_pkl_conf_loc.open("rb") as fin:
        eval_conf: EvalConf = pickle.load(fin)

    sentence_db = SentenceDB.load(eval_conf.sentence_db_loc)
    data_split = DataSplit.load(eval_conf.data_split_loc)
    q = FileQueue(queue_loc)
    tactic_client = tactic_gen_client_from_conf(eval_conf.tactic_conf)

    while True:
        try:
            file_info, idx = q.get()
        except EmptyFileQueueError:
            break

        proof_dp = file_info.get_dp(eval_conf.data_loc, sentence_db)

        location_info = LocationInfo(
            eval_conf.data_loc,
            file_info,
            eval_conf.split,
            proof_dp,
            idx,
            sentence_db,
            data_split,
        )
        run_conf = RunProofConf(
            location_info, eval_conf.search_conf, tactic_client, False, False
        )

        orig_summary = get_orig_summary(
            run_conf.file,
            run_conf.theorem,
            run_conf.loc.dp_proof_idx,
            run_conf.theorem_id,
            eval_conf,
        )
        save_loc = get_save_loc(orig_summary, eval_conf.save_loc)
        if save_loc.exists():
            with save_loc.open("r") as fin:
                save_data = json.load(fin)
            saved_summary = summary_from_json(save_data)
            if saved_summary.search_time is not None:
                _logger.info(
                    f"skipping proof of {run_conf.theorem_id} from {run_conf.file}"
                )
                continue

        save_summary(orig_summary, eval_conf.save_loc)

        _logger.info(f"running proof of {run_conf.theorem_id} from {run_conf.file}")
        worker_process = mp.Process(target=run_and_save_proof, args=(run_conf,))
        worker_process.start()
        worker_process.join(2 * run_conf.search_conf.timeout)
