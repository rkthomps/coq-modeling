from typing import Any
import os
import argparse
from pathlib import Path
import yaml
from tqdm import tqdm

from concurrent.futures import ProcessPoolExecutor, Future, as_completed


from data_management.splits import Split
from tactic_gen.tactic_data import TacticDataConf, LmDataset, ExampleCache


def get_i(dataset: LmDataset, i: int) -> Any:
    step_id = dataset.shuffled_idx.get_idx(dataset.split, i)
    get_cached = dataset.example_cache.get(
        step_id,
        dataset.formatter,
        dataset.data_loc,
        dataset.sentence_db,
    )
    return get_cached


def dataset_worker_mod_n(
    tactic_conf: TacticDataConf, split: Split, worker_id: int, n_workers: int
):
    dataset = LmDataset.from_conf(tactic_conf, split)
    for i in range(worker_id, len(dataset), n_workers):
        get_i(dataset, i)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--conf_loc",
        type=str,
        required=True,
        help="Location of the training config file.",
    )
    parser.add_argument(
        "--cache_loc", type=str, required=True, help="Location of the cache"
    )
    parser.add_argument("--n_workers", type=int, default=1)
    args = parser.parse_args()
    os.environ["TOKENIZERS_PARALLELISM"] = "false"

    conf_loc = Path(args.conf_loc)
    cache_loc = Path(args.cache_loc)
    n_workers: int = args.n_workers
    assert conf_loc.exists()
    if cache_loc.exists():
        raise FileExistsError(f"Cache already exists at {cache_loc}")

    os.makedirs(cache_loc, exist_ok=True)
    with open(args.conf_loc, "r") as fin:
        yaml_training_conf = yaml.safe_load(fin)

    conf = TacticDataConf.from_yaml(yaml_training_conf["tactic_data"])
    conf.cache_loc = cache_loc

    for split in Split:
        for i in range(n_workers):
            dataset_worker_mod_n(conf, split, i, n_workers)
