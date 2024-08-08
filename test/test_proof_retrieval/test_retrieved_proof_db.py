import random
import os
import yaml
import cProfile
import time
from data_management.dataset_file import DatasetFile
from data_management.sentence_db import SentenceDB
from pathlib import Path
from proof_retrieval.retrieved_proof_db import RetrievedProofDB
from proof_retrieval.retrieved_proof_db_creator import ProofDBCreatorConf
from tactic_gen.lm_example import formatter_conf_from_yaml, formatter_from_conf
from util.constants import DATA_POINTS_NAME


RETRIEVED_PROOF_LOC = Path("data/tfidf-proof-db")
DATA_LOC = Path("raw-data/coq-dataset")
SENTENCE_DB_LOC = Path("raw-data/coq-dataset/sentences.db")


class TestRetrievedProofDB:
    def test_retrieved_proof_db(self):
        if not RETRIEVED_PROOF_LOC.exists():
            return
        with (RETRIEVED_PROOF_LOC / RetrievedProofDB.CONF_NAME).open("r") as f:
            proof_db_conf = yaml.safe_load(f)
        proof_db_conf["proof_retriever_conf"]["cached_proof_loc"] = str(
            RETRIEVED_PROOF_LOC
        )

        formatter_conf_data = {
            "alias": "general",
            "num_proofs": 20,
            "proof_ret": proof_db_conf["proof_retriever_conf"],
        }

        formatter_conf = formatter_conf_from_yaml(formatter_conf_data)
        formatter = formatter_from_conf(formatter_conf)
        sentence_db = SentenceDB.load(SENTENCE_DB_LOC)
        # random.seed(0)
        # test_dps = random.sample(list(os.listdir(DATA_LOC / DATA_POINTS_NAME)), 50)
        test_dps = [
            "coq-community-gaia-theories-ordinals-ssete4.v",
            # "coq-community-gaia-theories-ordinals-ssete5.v",
        ]
        # test_dps = os.listdir(DATA_LOC / DATA_POINTS_NAME)[:5]
        for dp_name in test_dps:
            dp = DatasetFile.load(DATA_LOC / DATA_POINTS_NAME / dp_name, sentence_db)
            dp_training_time = 0
            dp_inference_time = 0
            print("Num proofs:", len(dp.proofs))
            print("Num steps:", sum(len(p.steps) for p in dp.proofs))
            for p_idx, proof in enumerate(dp.proofs[:3]):
                for s_idx, step in enumerate(proof.steps[:3]):
                    start1 = time.time()
                    example1 = formatter.example_from_step(
                        s_idx, p_idx, dp, training=False
                    )
                    end1 = time.time()
                    print("Step time:", end1 - start1)
                    # dp_inference_time += end1 - start1
                    # start2 = time.time()
                    # example2 = formatter.example_from_step(
                    #     s_idx, p_idx, dp, training=True
                    # )
                    # end2 = time.time()
                    # dp_training_time += end2 - start2
                    # assert example1 == example2
            # print(
            #     f"Processed {dp_name}. Inference time: {dp_inference_time}. Training time: {dp_training_time}"
            # )


if __name__ == "__main__":
    cProfile.run("TestRetrievedProofDB().test_retrieved_proof_db()")
