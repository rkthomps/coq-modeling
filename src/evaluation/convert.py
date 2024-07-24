import os
import json
import pickle
from pathlib import Path
import shutil
from tqdm import tqdm

from model_deployment.prove import (
    Summary,
    summary_to_json,
)
from data_management.dataset_file import DatasetFile
from data_management.sentence_db import SentenceDB


OLD_EVAL_LOC = Path("evaluations/old-result-format")
NEW_RESULT_LOC = Path("evaluations/json_fmt")


REPOS_LOC = Path("raw-data/coq-dataset/repos")
DP_LOC = Path("raw-data/coq-dataset/data_points")
SENTENCE_DB_LOC = Path("raw-data/coq-dataset/sentences.db")


class IdxThmMap:
    def __init__(self):
        self.cache: dict[tuple[str, int], str] = {}
        self.sentence_db = SentenceDB.load(SENTENCE_DB_LOC)

    def get_theorem_str(self, dp_name: str, idx: int) -> str:
        key = (dp_name, idx)
        if key in self.cache:
            return self.cache[key]
        dp_loc = DP_LOC / dp_name
        dp_obj = DatasetFile.load(dp_loc, self.sentence_db, metadata_only=True)
        for i, p in enumerate(dp_obj.proofs):
            self.cache[(dp_name, i)] = p.theorem.term.text
        return self.cache[key]


thm_map = IdxThmMap()
for eval_name in os.listdir(OLD_EVAL_LOC):
    old_eval_name_loc = OLD_EVAL_LOC / eval_name
    new_eval_name_loc = NEW_RESULT_LOC / eval_name
    os.makedirs(new_eval_name_loc)
    shutil.copy(old_eval_name_loc / "conf.yaml", new_eval_name_loc)
    print("Processing", eval_name)
    for result in tqdm(os.listdir(old_eval_name_loc)):
        if result == "conf.yaml":
            continue
        result_loc = old_eval_name_loc / result
        with result_loc.open("rb") as fin:
            r: Summary = pickle.load(fin)

        dp_name = str(r.file.relative_to(REPOS_LOC)).replace("/", "-")
        proof_idx = int(r.theorem.split("-")[-1])
        thm_str = thm_map.get_theorem_str(dp_name, proof_idx)

        json_data = r.to_json()
        json_data["proof_idx"] = proof_idx
        json_data["theorem"] = thm_str
        json_data["theorem_id"] = r.theorem

        assert result.endswith(".pkl")
        out_loc = (new_eval_name_loc / result).with_suffix(".json")

        os.makedirs(out_loc.parent, exist_ok=True)
        with out_loc.open("w") as fout:
            fout.write(json.dumps(json_data, indent=2))
