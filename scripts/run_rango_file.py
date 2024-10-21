import os
import argparse
from pathlib import Path
from data_management.dataset_file import DatasetFile
from data_management.splits import FileInfo, DataSplit, Split
from data_management.sentence_db import SentenceDB
from data_management.create_file_data_point import get_data_point
from model_deployment.straight_line_searcher import StraightLineSearcherConf

from model_deployment.conf_utils import (
    tactic_gen_to_client_conf,
    start_servers,
    wait_for_servers,
)
from model_deployment.prove import RunProofConf, LocationInfo, run_proof
from model_deployment.tactic_gen_client import (
    DecoderTacticGenConf,
    tactic_conf_update_ips,
    tactic_gen_client_from_conf,
)

from util.util import set_rango_logger
from util.util import clear_port_map
from util.constants import RANGO_LOGGER

import logging


def find_proof(theorem_name: str, dp: DatasetFile) -> int:
    for i, proof in enumerate(dp.proofs):
        if theorem_name in proof.theorem.term.text:
            return i
    raise ValueError(f"Could not find proof for theorem: {theorem_name}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("file")
    parser.add_argument("theorem_name")
    parser.add_argument("checkpoint_loc")

    args = parser.parse_args()

    file = Path(args.file)
    checkpoint_loc = Path(args.checkpoint_loc)
    sentence_db_loc = Path("./tmp-sentences.db")
    if sentence_db_loc.exists():
        os.remove(sentence_db_loc)
    sentence_db = SentenceDB.create(sentence_db_loc)

    assert file.exists()
    assert checkpoint_loc.exists()

    set_rango_logger(__file__, logging.DEBUG)

    dp = get_data_point(file, Path("."), sentence_db, False, None)

    psuedo_file_info = FileInfo(
        "psuedo-file.v",
        dp.file_context.file,
        dp.file_context.workspace,
        dp.file_context.workspace,
    )
    psuedo_split = DataSplit([], [], [])
    thm_idx = find_proof(args.theorem_name, dp)
    loc = LocationInfo(
        Path("."),
        psuedo_file_info,
        Split.TEST,
        dp,
        thm_idx,
        sentence_db,
        psuedo_split,
    )

    search_conf = StraightLineSearcherConf(600, True, None, None)

    conf = DecoderTacticGenConf(checkpoint_loc, None)
    tactic_conf, next_num, commands = tactic_gen_to_client_conf(conf, 0)

    if 0 < len(commands):
        clear_port_map()
        procs = start_servers(commands)
        port_map = wait_for_servers(next_num)
        tactic_conf_update_ips(tactic_conf, port_map)

    tactic_client = tactic_gen_client_from_conf(tactic_conf)

    conf = RunProofConf(loc, search_conf, tactic_client, True, False)
    run_proof(conf)
