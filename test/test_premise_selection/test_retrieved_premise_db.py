import os
import yaml
import time
from data_management.dataset_file import DatasetFile
from data_management.sentence_db import SentenceDB
from pathlib import Path
from premise_selection.retrieved_premise_db import RetrievedPremiseDB
from tactic_gen.lm_example import (
    formatter_conf_from_yaml,
    formatter_from_conf,
    formatter_update_ips,
)
from model_deployment.conf_utils import (
    formatter_conf_to_client_conf,
    start_servers,
    wait_for_servers,
)

from util.util import clear_port_map
from util.constants import DATA_POINTS_NAME


RETRIEVED_PREMISE_LOC = Path("data/tfidf-proj-thm-prem-db")
DATA_LOC = Path("raw-data/coq-dataset")
SENTENCE_DB_LOC = Path("raw-data/coq-dataset/sentences.db")


class TestRetrievedPremiseDB:
    def test_retrieved_premise_db(self):
        if not RETRIEVED_PREMISE_LOC.exists():
            return
        with (RETRIEVED_PREMISE_LOC / RetrievedPremiseDB.CONF_NAME).open("r") as f:
            proof_db_conf = yaml.safe_load(f)
        proof_db_conf["premise_conf"]["cached_premise_loc"] = str(RETRIEVED_PREMISE_LOC)
        proof_db_conf["premise_conf"]["sentence_db_loc"] = str(SENTENCE_DB_LOC)

        formatter_conf_data = {
            "alias": "general",
            "num_premises": 50,
            "premise": proof_db_conf["premise_conf"],
        }

        formatter_conf = formatter_conf_from_yaml(formatter_conf_data)
        formatter_client_conf, next_num, commands = formatter_conf_to_client_conf(
            formatter_conf, 0
        )
        if 0 < len(commands):
            clear_port_map()
            start_servers(commands)
            port_map = wait_for_servers(next_num)
            formatter_update_ips(formatter_client_conf, port_map)

        formatter = formatter_from_conf(formatter_client_conf)
        sentence_db = SentenceDB.load(SENTENCE_DB_LOC)
        for dp_name in os.listdir(DATA_LOC / DATA_POINTS_NAME)[:10]:
            dp = DatasetFile.load(DATA_LOC / DATA_POINTS_NAME / dp_name, sentence_db)
            total_train_time = 0
            total_inference_time = 0
            for p_idx, proof in enumerate(dp.proofs):
                for s_idx, step in enumerate(proof.steps):
                    start1 = time.time()
                    example1 = formatter.example_from_step(
                        s_idx, p_idx, dp, training=False
                    )
                    end1 = time.time()
                    total_inference_time += end1 - start1
                    start2 = time.time()
                    example2 = formatter.example_from_step(
                        s_idx, p_idx, dp, training=True
                    )
                    end2 = time.time()
                    total_train_time += end2 - start2
                    try:
                        assert example1 == example2
                    except AssertionError:
                        print("Example 1 ==============")
                        print(example1.premises)
                        print("Example 2 ==============")
                        print(example2.premises)
            print(
                f"Processed {dp_name}; train time: {total_train_time}; inference time: {total_inference_time}"
            )


if __name__ == "__main__":
    TestRetrievedPremiseDB().test_retrieved_premise_db()
