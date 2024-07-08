import sys, os
import argparse
import pickle
import time
from pathlib import Path
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


def get_orig_summary(file: Path, theorem: str, eval_conf: EvalConf) -> Summary:
    match eval_conf.search_conf:
        case MCTSConf():
            return MCTSSummary.from_search_result(file, theorem, None)
        case ClassicalSearchConf():
            return ClassicalSummary.from_search_result(file, theorem, None)
        case StraightLineSearcherConf():
            return StraightLineSummary.from_search_result(file, theorem, None)


def run_and_save_proof(run_conf: RunProofConf):
    _logger.info(f"running proof of {theorem_name} from {file}")
    result = run_proof(run_conf)
    summary = summary_from_result(file, theorem_name, result)
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
        tactic_client = tactic_gen_client_from_conf(eval_conf.tactic_conf)
        run_conf = RunProofConf(
            location_info, eval_conf.search_conf, tactic_client, False, False
        )

        file = eval_conf.data_loc / location_info.file_info.file
        try:
            theorem_name = (
                run_conf.loc.dataset_file.proofs[
                    run_conf.loc.dp_proof_idx
                ].get_theorem_name()
                + "-"
                + str(run_conf.loc.dp_proof_idx)
            )
        except ValueError:
            _logger.info(
                f"Could not get name of theorem for: {run_conf.loc.dataset_file.proofs[run_conf.loc.dp_proof_idx]}"
            )
            continue

        orig_summary = get_orig_summary(file, theorem_name, eval_conf)
        save_summary(orig_summary, eval_conf.save_loc)

        _logger.info(f"running proof of {theorem_name} from {file}")
        worker_process = mp.Process(target=run_and_save_proof, args=(run_conf,))
        worker_process.start()
        worker_process.join(2 * run_conf.search_conf.timeout)
