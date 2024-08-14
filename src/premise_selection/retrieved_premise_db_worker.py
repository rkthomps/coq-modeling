from pathlib import Path
import json
import time

from premise_selection.retrieved_premise_db import (
    RetrievedPremiseDB,
    PremiseDBPage,
    StepID,
)
from premise_selection.rerank_client import (
    PremiseClient,
    premise_client_from_conf,
    premise_conf_update_ips,
)
from premise_selection.retrieved_premise_db_creator import PremiseDBCreatorConf

from model_deployment.conf_utils import (
    premise_conf_to_client_conf,
    start_servers,
    wait_for_servers,
)

from util.file_queue import FileQueue, EmptyFileQueueError
from util.slurm import worker_get_conf_queue
from util.util import get_basic_logger, clear_port_map

from data_management.sentence_db import SentenceDB
from data_management.splits import FileInfo
from data_management.dataset_file import Sentence

_logger = get_basic_logger(__name__)


def process_f_info(
    f_info: FileInfo,
    max_num_premises: int,
    data_loc: Path,
    save_loc: Path,
    sentence_db: SentenceDB,
    premise_client: PremiseClient,
):
    start = time.time()
    file_dp = f_info.get_dp(data_loc, sentence_db)
    file_page_dict: dict[StepID, list[Sentence]] = {}
    for proof_idx, proof in enumerate(file_dp.proofs):
        for step_idx, step in enumerate(proof.steps):
            step_id = StepID(file_dp.dp_name, proof_idx, step_idx)
            filter_result = premise_client.premise_filter.get_pos_and_avail_premises(
                step, proof, file_dp
            )
            premise_generator = premise_client.get_ranked_premises(
                step_idx, proof, file_dp, filter_result.avail_premises, training=False
            )
            retrieved_sentences = list(premise_generator)[:max_num_premises]
            file_page_dict[step_id] = retrieved_sentences
    new_page = PremiseDBPage(file_page_dict)

    with open(save_loc / f_info.dp_name, "w") as f:
        json.dump(new_page.to_json(sentence_db), f, indent=2)
    end = time.time()
    _logger.info(f"Processed {f_info.dp_name} in {end - start:.2f} seconds.")


if __name__ == "__main__":
    conf_loc, queue_loc = worker_get_conf_queue()
    conf = PremiseDBCreatorConf.load(conf_loc)
    queue = FileQueue(queue_loc)

    sentence_db = SentenceDB.load(conf.sentence_db_loc)
    premise_conf, next_num, commands = premise_conf_to_client_conf(conf.premise_conf, 0)
    if 0 < len(commands):
        clear_port_map()
        start_servers(commands)
        port_map = wait_for_servers(next_num)
        premise_conf_update_ips(premise_conf, port_map)

    premise_client = premise_client_from_conf(premise_conf)

    while True:
        try:
            f_info = queue.get()
            process_f_info(
                f_info,
                conf.max_num_premises,
                conf.data_loc,
                conf.save_loc,
                sentence_db,
                premise_client,
            )
        except EmptyFileQueueError:
            break
