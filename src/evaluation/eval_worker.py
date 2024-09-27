import argparse
import json
import pickle
import yaml
import time
from pathlib import Path
import subprocess
import multiprocessing as mp

from data_management.splits import DataSplit, FileInfo
from data_management.sentence_db import SentenceDB
from evaluation.eval_utils import ProofMap, EvalConf

from model_deployment.conf_utils import (
    tactic_gen_to_client_conf,
    wait_for_servers,
    start_servers,
)
from model_deployment.classical_searcher import ClassicalSearchConf
from model_deployment.straight_line_searcher import StraightLineSearcherConf
from model_deployment.whole_proof_searcher import WholeProofSearcherConf
from model_deployment.prove import (
    LocationInfo,
    RunProofConf,
    run_proof,
    summary_from_result,
    save_summary,
    summary_from_json,
    pretty_print_summary,
    ClassicalSummary,
    StraightLineSummary,
    WholeProofSummary,
    Summary,
)
from model_deployment.tactic_gen_client import (
    tactic_gen_client_from_conf,
    tactic_conf_update_ips,
)
from util.constants import CLEAN_CONFIG, RANGO_LOGGER
from util.util import set_rango_logger, clear_port_map
from util.file_queue import FileQueue, EmptyFileQueueError

import logging


_logger = logging.getLogger(RANGO_LOGGER)


def get_orig_summary(
    file: Path, theorem: str, proof_idx: int, theorem_id: str, eval_conf: EvalConf
) -> Summary:
    match eval_conf.search_conf:
        case ClassicalSearchConf():
            return ClassicalSummary.from_search_result(
                file, theorem, proof_idx, theorem_id, None
            )
        case StraightLineSearcherConf():
            return StraightLineSummary.from_search_result(
                file, theorem, proof_idx, theorem_id, None
            )
        case WholeProofSearcherConf():
            return WholeProofSummary.from_search_result(
                file, theorem, proof_idx, theorem_id, None
            )


def run_and_save_proof(run_conf: RunProofConf):
    try:
        result = run_proof(run_conf)
    except TimeoutError:
        _logger.error(
            f"Got timeout error running proof: {run_conf.theorem_id} from {run_conf.file}"
        )
        return
    summary = summary_from_result(
        run_conf.file,
        run_conf.theorem,
        run_conf.loc.dp_proof_idx,
        run_conf.theorem_id,
        result,
    )
    _logger.info(pretty_print_summary(summary))
    save_summary(summary, run_conf.loc.file_info, eval_conf.save_loc)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--conf_loc", required=True, help="Location of eval configuration."
    )
    parser.add_argument(
        "--queue_loc", required=True, help="Location of the work queue."
    )

    args = parser.parse_args()
    conf_loc = Path(args.conf_loc)
    queue_loc = Path(args.queue_loc)

    set_rango_logger(__file__, logging.DEBUG)

    assert conf_loc.exists()
    assert queue_loc.exists()

    with conf_loc.open("r") as fin:
        yaml_conf = yaml.safe_load(fin)

    eval_conf = EvalConf.from_yaml(yaml_conf)

    switch = subprocess.run(["opam", "switch", "show"], capture_output=True)
    _logger.info(f"Running with switch {switch.stdout.decode()}")

    sentence_db = SentenceDB.load(eval_conf.sentence_db_loc)
    data_split = DataSplit.load(eval_conf.data_split_loc)
    q = FileQueue(queue_loc)

    clean_tactic_conf, n_commands, commands = tactic_gen_to_client_conf(
        eval_conf.tactic_conf, 0
    )
    procs = []
    if 0 < len(commands):
        clear_port_map()
        procs = start_servers(commands)
        port_map = wait_for_servers(n_commands)
        tactic_conf_update_ips(clean_tactic_conf, port_map)

    tactic_client = tactic_gen_client_from_conf(clean_tactic_conf)
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
        save_summary(orig_summary, file_info, eval_conf.save_loc)

        _logger.info(f"running proof of {run_conf.theorem_id} from {run_conf.file}")
        worker_process = mp.Process(target=run_and_save_proof, args=(run_conf,))
        worker_process.start()
        worker_process.join(2 * run_conf.search_conf.timeout)

    for p in procs:
        p.kill()
