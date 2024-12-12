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
from evaluation.eval_utils import EvalConf
from evaluation.find_coqstoq_idx import get_thm_desc

from model_deployment.conf_utils import (
    tactic_gen_to_client_conf,
    wait_for_servers,
    start_servers,
    StartModelCommand,
)
from model_deployment.classical_searcher import ClassicalSearchConf
from model_deployment.straight_line_searcher import StraightLineSearcherConf
from model_deployment.whole_proof_searcher import WholeProofSearcherConf
from model_deployment.prove import (
    LocationInfo,
    RunProofConf,
    run_proof,
    get_save_loc,
    RangoResult,
    load_result,
)
from model_deployment.tactic_gen_client import (
    tactic_gen_client_from_conf,
    tactic_conf_update_ips,
    TacticGenConf,
    TacticGenClient,
)
from util.constants import CLEAN_CONFIG, RANGO_LOGGER
from util.util import set_rango_logger, clear_port_map
from util.file_queue import FileQueue, EmptyFileQueueError
from util.coqstoq_utils import get_file_loc, get_workspace_loc

import logging
from coqstoq import EvalTheorem


_logger = logging.getLogger(RANGO_LOGGER)


def run_and_save_proof(thm: EvalTheorem, run_conf: RunProofConf, save_dir: Path):
    start = time.time()
    save_loc = get_save_loc(save_dir, thm)
    try:
        result = run_proof(run_conf)
        rango_result = RangoResult.from_search_result(thm, result)
    except TimeoutError:
        _logger.error(
            f"Got timeout error running proof: {run_conf.theorem_id} from {run_conf.loc.file_loc}"
        )
        stop = time.time()
        rango_result = RangoResult(thm, None, stop - start, None)

    rango_result.save(save_loc)
    if rango_result.proof is not None:
        _logger.info(f"Eval theorem for {thm.path}::{run_conf.theorem_id} : SUCCESS")
    else:
        _logger.info(f"Eval theorem for {thm.path} : FAILURE")


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

    q = FileQueue[EvalTheorem](queue_loc)

    clean_tactic_confs: list[TacticGenConf] = []
    all_commands: list[StartModelCommand] = []
    next_num = 0
    for tactic_conf in eval_conf.tactic_confs:
        clean_tactic_conf, n_commands, commands = tactic_gen_to_client_conf(
            tactic_conf, next_num
        )
        clean_tactic_confs.append(clean_tactic_conf)
        all_commands.extend(commands)
        next_num = n_commands

    procs = []
    if 0 < len(all_commands):
        clear_port_map()
        procs = start_servers(all_commands)
        port_map = wait_for_servers(next_num)
        for tactic_conf in clean_tactic_confs:
            tactic_conf_update_ips(tactic_conf, port_map)

    tactic_clients: list[TacticGenClient] = [
        tactic_gen_client_from_conf(conf) for conf in clean_tactic_confs
    ]

    strikes = 0
    MAX_STRIKES_IN_A_ROW = 3
    while True:
        try:
            eval_thm = q.get()
        except EmptyFileQueueError:
            break

        thm_desc = get_thm_desc(eval_thm, eval_conf.data_loc, sentence_db)
        if thm_desc is None:
            _logger.error(f"Failed to get thm desc for {eval_thm}")
            continue
        assert thm_desc is not None

        proof_dp = thm_desc.dp

        location_info = LocationInfo(
            eval_conf.data_loc,
            get_file_loc(eval_thm, eval_conf.coqstoq_loc),
            get_workspace_loc(eval_thm, eval_conf.coqstoq_loc),
            proof_dp,
            thm_desc.idx,
            sentence_db,
        )
        run_conf = RunProofConf(
            location_info, eval_conf.search_conf, tactic_clients, False, False
        )
        orig_summary = RangoResult(eval_thm, None, None, None)
        save_loc = get_save_loc(eval_conf.save_loc, eval_thm)
        if save_loc.exists():
            _logger.info(f"Skipping {eval_thm.path}::{run_conf.theorem_id}")
            continue

        orig_summary.save(save_loc)
        _logger.info(
            f"running proof of {run_conf.theorem_id} from {location_info.file_loc}"
        )
        worker_process = mp.Process(
            target=run_and_save_proof, args=(eval_thm, run_conf, eval_conf.save_loc)
        )
        worker_process.start()
        worker_process.join(2 * run_conf.search_conf.timeout)
        assert save_loc.exists()
        result = load_result(save_loc)
        if result.time is None:
            strikes += 1
        else:
            strikes = 0
        if MAX_STRIKES_IN_A_ROW <= strikes:
            _logger.error(f"Too many strikes for {eval_thm.path}")
            break
    for p in procs:
        p.kill()
