import os
import json
import shutil
from pathlib import Path
from tqdm import tqdm

from model_deployment.prove import (
    ClassicalSummary,
    MCTSSummary,
    StraightLineSummary,
    Summary,
)

OLD_LOC = Path("evaluations/eval-results-no-alias")
NEW_LOC = Path("evaluations/eval-results")


for eval in tqdm(os.listdir(OLD_LOC)):
    old_eval_loc = OLD_LOC / eval
    new_eval_loc = NEW_LOC / eval
    os.makedirs(new_eval_loc)
    shutil.copy(old_eval_loc / "conf.yaml", new_eval_loc)
    for f in os.listdir(old_eval_loc):
        if f == "conf.yaml":
            continue
        assert f.endswith(".json")
        with (old_eval_loc / f).open("r") as fin:
            json_data = json.load(fin)
            if "num_nodes_pruned" in json_data:
                new_json_data = json_data | {"alias": ClassicalSummary.ALIAS}
            elif "attempts" in json_data:
                new_json_data = json_data | {"alias": StraightLineSummary.ALIAS}
            else:
                raise ValueError("Unknown summary")

        with (new_eval_loc / f).open("w") as fout:
            fout.write(json.dumps(new_json_data, indent=2))
