import sys, os
import pickle
import time
import signal

import argparse
import requests
import subprocess
from pathlib import Path
from dataclasses import dataclass
import yaml

from model_deployment.conf_utils import (
    TopLevelConf,
    to_client_conf,
    merge,
    get_ip,
    update_ips,
    get_flexible_url,
    read_port_map,
    clear_port_map,
    START_PORT,
)

from model_deployment.run_proof import TestProofConf
from model_deployment.run_proofs import TestProofsConf
from model_deployment.run_whole_proof import TestWholeProofConf
from model_deployment.run_whole_proofs import TestWholeProofsConf
from evaluation.evaluate import EvalConf

from premise_selection.evaluate import PremiseEvalConf
from data_management.create_lm_dataset import LmDatasetConf
from data_management.create_rerank_dataset import RerankDatasetConf
from data_management.create_premise_dataset import SelectDataConfig
from data_management.create_goal_dataset import GoalDatasetConf

from util.constants import SERVER_LOC, CLEAN_CONFIG, PORT_MAP_LOC


@dataclass
class Command:
    conf: type[TopLevelConf]
    py_path: Path


COMMANDS = {
    "prove": Command(TestProofConf, Path("src/model_deployment/run_proof.py")),
    "run-dev": Command(TestProofsConf, Path("src/model_deployment/run_proofs.py")),
    "eval": Command(EvalConf, Path("src/evaluation/evaluate.py")),
    "prove-whole": Command(
        TestWholeProofConf, Path("src/model_deployment/run_whole_proof.py")
    ),
    "run-dev-whole": Command(
        TestWholeProofsConf, Path("src/model_deployment/run_whole_proofs.py")
    ),
    "select-data": Command(
        SelectDataConfig, Path("src/data_management/create_premise_dataset.py")
    ),
    "rerank-data": Command(
        RerankDatasetConf, Path("src/data_management/create_rerank_dataset.py")
    ),
    "lm-data": Command(LmDatasetConf, Path("src/data_management/create_lm_dataset.py")),
    "goal-data": Command(
        GoalDatasetConf, Path("src/data_management/create_goal_dataset.py")
    ),
    "eval-premise": Command(PremiseEvalConf, Path("src/premise_selection/evaluate.py")),
}


class CommandNotFoundError(Exception):
    pass


class ServerFailedError(Exception):
    pass


def wait_for_servers(
    num_ports: int,
    open_processes: list[subprocess.Popen[bytes]],
) -> dict[int, str]:
    session = requests.Session()
    urls: list[str] = []

    cur_port_map = read_port_map()
    while len(cur_port_map) < num_ports:
        time.sleep(1)
        cur_port_map = read_port_map()
        print("Cur port map:", cur_port_map)

    for port_incr in range(next_server_num):
        port = START_PORT + port_incr
        url = get_flexible_url(cur_port_map[port], port).get_url()
        urls.append(url)

    assert len(open_processes) == len(urls)
    for process, server_url in zip(started_processes, urls):
        while True:
            try:
                poll_result = subprocess.Popen.poll(process)
                if poll_result is not None:
                    raise ServerFailedError
                response = session.get(server_url)
                break
            except requests.exceptions.RequestException:
                continue
    return cur_port_map


if __name__ == "__main__":
    command_list = ", ".join(COMMANDS.keys())
    parser = argparse.ArgumentParser()
    parser.add_argument("command", help=f"Select from: {command_list}")
    parser.add_argument("config", help="Yaml configuration file for command.")
    parser.add_argument(
        "devices",
        nargs="*",
        type=int,
        help="CUDA devices to use for running the command.",
    )
    args = parser.parse_args(sys.argv[1:])

    clear_port_map()

    if args.command not in COMMANDS:
        raise (CommandNotFoundError(f"{args.command} not one of {command_list}"))

    if not Path(SERVER_LOC).exists():
        os.makedirs(SERVER_LOC)

    command = COMMANDS[args.command]
    config_loc = Path(args.config)
    if not config_loc.exists():
        raise FileNotFoundError(f"{config_loc}")

    with config_loc.open("r") as fin:
        yaml_conf = yaml.load(fin, Loader=yaml.Loader)

    top_level_conf = command.conf.from_yaml(yaml_conf)
    print(top_level_conf)
    clean_conf_path = Path(f"./{CLEAN_CONFIG}")
    started_processes: list[subprocess.Popen[bytes]] = []
    try:
        next_server_num = 0
        clean_top_level_confs: list[TopLevelConf] = []
        for d in args.devices:
            clean_top_level_conf, next_server_num, commands = to_client_conf(
                top_level_conf, next_server_num
            )
            clean_top_level_confs.append(clean_top_level_conf)
            env = os.environ | {"CUDA_VISIBLE_DEVICES": f"{d}"}
            for c in commands:
                process = subprocess.Popen(c.to_list(), env=env)
                started_processes.append(process)

        clean_top_level_conf = merge(clean_top_level_confs)

        print("Merged conf:")
        print(clean_top_level_conf)
        print("Waiting for servers to start...")
        port_map = wait_for_servers(next_server_num, started_processes)
        update_ips(clean_top_level_conf, port_map)

        with clean_conf_path.open("wb") as fout:
            pickle.dump(clean_top_level_conf, fout)
        subprocess.run(["python3", command.py_path, args.config])
    finally:
        if clean_conf_path.exists():
            os.remove(clean_conf_path)
        for p in started_processes:
            p.send_signal(signal.SIGINT)
