import sys, os
import shutil
import pickle
import argparse
from pathlib import Path
from datetime import datetime
from subprocess import Popen

import yaml
from evaluation.eval_utils import PremiseEvalConf, initialize_and_fill_queue_premise

from util.constants import CLEAN_CONFIG, QUEUE_NAME, TMP_LOC


def start_evaluators(
    n_workers: int, eval_conf_loc: Path, eval_queue_loc: Path
) -> list[Popen[bytes]]:
    worker_procs: list[Popen[bytes]] = []
    for _ in range(n_workers):
        worker_cmd = [
            "python3",
            "src/evaluation/premise_eval_worker.py",
            eval_conf_loc,
            eval_queue_loc,
        ]
        worker_proc = Popen(worker_cmd)
        worker_procs.append(worker_proc)
    return worker_procs


def run(
    eval_conf: PremiseEvalConf,
    n_workers: int,
    device_list: list[int],
):
    time_str = datetime.now().strftime("%m%d%H%M%S")
    eval_conf_loc = TMP_LOC / (CLEAN_CONFIG + "-" + time_str)
    eval_queue_loc = TMP_LOC / (QUEUE_NAME + "-" + time_str)
    initialize_and_fill_queue_premise(eval_queue_loc, eval_conf)
    # server_procs = start_servers_and_update_conf(eval_conf, device_list, eval_conf_loc)
    with eval_conf_loc.open("wb") as fout:
        pickle.dump(eval_conf, fout)
    worker_procs = start_evaluators(
        n_workers,
        eval_conf_loc,
        eval_queue_loc,
    )
    for w in worker_procs:
        w.wait()
    for w in worker_procs:
        w.kill()


if __name__ == "__main__":
    parser = argparse.ArgumentParser("Local premise selection evaluation.")
    parser.add_argument("conf_loc", help="Location of eval configuration")
    parser.add_argument("n_workers", type=int, help="Number of workers to use.")
    parser.add_argument(
        "device_list", type=int, nargs="+", help="List of gpu devices to use."
    )
    args = parser.parse_args(sys.argv[1:])

    conf_loc = Path(args.conf_loc)
    n_workers = args.n_workers
    device_list = args.device_list

    assert conf_loc.exists()
    assert isinstance(n_workers, int)
    assert isinstance(device_list, list)

    with conf_loc.open("r") as fin:
        conf = yaml.load(fin, Loader=yaml.Loader)

    eval_conf = PremiseEvalConf.from_yaml(conf)
    if eval_conf.save_loc.exists():
        raise FileExistsError(f"{eval_conf.save_loc}")
        # answer = input(f"{eval_conf.save_loc} already exists. Overwrite? y/n: ")
        # if answer.lower() != "y":
        #     raise FileExistsError(f"{eval_conf.save_loc}")
        # shutil.rmtree(eval_conf.save_loc)

    os.makedirs(eval_conf.save_loc)
    shutil.copy(conf_loc, eval_conf.save_loc / "conf.yaml")
    run(eval_conf, n_workers, device_list)
