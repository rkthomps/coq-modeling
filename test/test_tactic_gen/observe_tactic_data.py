import time
import yaml
from pathlib import Path
from data_management.splits import Split
from tactic_gen.tactic_data import LmDatasest, TacticDataConf

TRAIN_CONF_LOC = Path("confs/train/decoder.yaml")

with TRAIN_CONF_LOC.open("r") as f:
    train_conf = yaml.safe_load(f)

tactic_data_conf = TacticDataConf.from_yaml(train_conf["tactic_data"])
dataset = LmDatasest.from_conf(tactic_data_conf, Split.TRAIN)

for i in range(len(dataset)):
    start = time.time()
    example = dataset[i]
    end = time.time()
    print(
        f"Time taken to get example {i} (Cached {dataset.example_cache.num_cached}): {end - start}"
    )
