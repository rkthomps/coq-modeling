from pathlib import Path
import json
import time

from proof_retrieval.retrieved_proof_db_creator import ProofDBCreatorConf
from proof_retrieval.retrieved_proof_db import RetrievedProofDB, StepID, ProofDBPage
from proof_retrieval.proof_retriever import (
    ProofRetriever,
    proof_retriever_from_conf,
    proof_conf_update_ips,
)
from proof_retrieval.retrieved_proof_db_creator import ProofDBCreatorConf

from model_deployment.conf_utils import (
    proof_conf_to_client_conf,
    start_servers,
    wait_for_servers,
)

from util.file_queue import FileQueue, EmptyFileQueueError
from util.slurm import worker_get_conf_queue

from data_management.sentence_db import SentenceDB
from data_management.splits import FileInfo

from util.util import set_rango_logger, clear_port_map
from util.constants import RANGO_LOGGER
import logging

_logger = logging.getLogger(RANGO_LOGGER)


def process_f_info(
    f_info: FileInfo,
    data_loc: Path,
    save_loc: Path,
    sentence_db: SentenceDB,
    proof_retriever: ProofRetriever,
):
    start = time.time()
    file_dp = f_info.get_dp(data_loc, sentence_db)
    file_page_dict: dict[StepID, list[StepID]] = {}
    for proof_idx, proof in enumerate(file_dp.proofs):
        for step_idx, step in enumerate(proof.steps):
            step_id = StepID(file_dp.dp_name, proof_idx, step_idx)
            retrieved_steps = proof_retriever.get_similar_proof_steps(
                step_idx, proof, file_dp, training=False
            )
            retrieved_step_ids = [step_id for _, step_id in retrieved_steps]
            file_page_dict[step_id] = retrieved_step_ids
    new_page = ProofDBPage(file_page_dict)
    with open(save_loc / f_info.dp_name, "w") as f:
        json.dump(new_page.to_json(), f, indent=2)
    end = time.time()
    _logger.info(f"Processed {f_info.dp_name} in {end - start:.2f} seconds.")


if __name__ == "__main__":
    set_rango_logger(__file__, logging.DEBUG)
    conf_loc, queue_loc = worker_get_conf_queue()
    conf = ProofDBCreatorConf.load(conf_loc)
    queue = FileQueue(queue_loc)

    sentence_db = SentenceDB.load(conf.sentence_db_loc)
    proof_ret_conf, next_num, commands = proof_conf_to_client_conf(
        conf.proof_retriever_conf, 0
    )
    if 0 < len(commands):
        clear_port_map()
        start_servers(commands)
        port_map = wait_for_servers(next_num)
        proof_conf_update_ips(proof_ret_conf, port_map)

    proof_retriever = proof_retriever_from_conf(proof_ret_conf)

    while True:
        try:
            f_info = queue.get()
            if (conf.save_loc / f_info.dp_name).exists():
                _logger.info(f"Skipping {f_info.dp_name}")
                continue
            process_f_info(
                f_info,
                conf.data_loc,
                conf.save_loc,
                sentence_db,
                proof_retriever,
            )
        except EmptyFileQueueError:
            break
