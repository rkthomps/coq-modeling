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

from data_management.create_lm_dataset import LmDatasetConf
from data_management.create_rerank_dataset import RerankDatasetConf
from data_management.create_premise_dataset import SelectDataConfig
from data_management.create_goal_dataset import GoalDatasetConf
from premise_selection.premise_filter import PremiseFilterConf
from premise_selection.rerank_formatter import RerankFormatterConf
from premise_selection.evaluate import PremiseEvalConf

from tactic_gen.lm_example import (
    FormatterConf,
    PremiseFormatterConf,
    GPTPremiseFormatterConf,
)
from model_deployment.premise_client import (
    PremiseConf,
    SelectConf,
    SelectClientConf,
    RerankConf,
    RerankClientConf,
)
from model_deployment.tactic_gen_client import (
    TacticGenConf,
    FidTacticGenConf,
    LocalTacticGenClientConf,
)
from model_deployment.run_proof import TestProofConf
from model_deployment.run_proofs import TestProofsConf
from model_deployment.run_whole_proof import TestWholeProofConf
from model_deployment.run_whole_proofs import TestWholeProofsConf
from util.constants import (
    PREMISE_DATA_CONF_NAME,
    RERANK_DATA_CONF_NAME,
    DATA_CONF_NAME,
    CLEAN_CONFIG,
)


TopLevelConf = (
    LmDatasetConf
    | TestProofConf
    | TestProofsConf
    | TestWholeProofConf
    | TestWholeProofsConf
    | RerankDatasetConf
    | GoalDatasetConf
    | PremiseEvalConf
)

next_port = 8000
open_servers: list[str] = []
started_processes: list[subprocess.Popen[bytes]] = []

SELECT_SERVER_SCRIPT = Path("src/model_deployment/select_server.py")
RERANK_SERVER_SCRIPT = Path("src/model_deployment/rerank_server.py")
TACTIC_GEN_SERVER_SCRIPT = Path("src/model_deployment/tactic_gen_server.py")


def __make_select_command(select_conf: SelectConf) -> list[str]:
    if select_conf.vector_db_loc is None:
        command = [
            "python3",
            f"{SELECT_SERVER_SCRIPT}",
            f"{select_conf.checkpoint_loc}",
            f"{next_port}",
        ]
    else:
        command = [
            "python3",
            f"{SELECT_SERVER_SCRIPT}",
            "--vector_db_loc",
            f"{select_conf.vector_db_loc}",
            f"{select_conf.checkpoint_loc}",
            f"{next_port}",
        ]
    return command


def start_select_servers(select_conf: SelectConf, use_devices: list[int]) -> list[str]:
    global next_port
    urls: list[str] = []
    for device in use_devices:
        env = os.environ | {"CUDA_VISIBLE_DEVICES": f"{device}"}
        command = __make_select_command(select_conf)
        process = subprocess.Popen(command, env=env)
        url = f"http://localhost:{next_port}"
        open_servers.append(url)
        urls.append(url)
        next_port += 1
        started_processes.append(process)
    return urls


def start_rerank_servers(rerank_conf: RerankConf, use_devices: list[int]) -> list[str]:
    global next_port
    urls: list[str] = []
    for device in use_devices:
        env = os.environ | {"CUDA_VISIBLE_DEVICES": f"{device}"}
        command = [
            "python3",
            RERANK_SERVER_SCRIPT,
            f"{rerank_conf.checkpoint_loc}",
            f"{next_port}",
        ]
        process = subprocess.Popen(command, env=env)
        url = f"http://localhost:{next_port}"
        open_servers.append(url)
        urls.append(url)
        next_port += 1
        started_processes.append(process)
    return urls


def start_servers_premise_conf(
    conf: PremiseConf, use_devices: list[int]
) -> PremiseConf:
    match conf:
        case SelectConf():
            urls = start_select_servers(conf, use_devices)
            assert 0 < len(conf.checkpoint_loc.parents)
            model_loc = conf.checkpoint_loc.parents[0]
            data_conf_loc = model_loc / PREMISE_DATA_CONF_NAME
            assert data_conf_loc.exists()
            with data_conf_loc.open("r") as fin:
                yaml_data = yaml.load(fin, Loader=yaml.Loader)
            data_conf = SelectDataConfig.from_yaml(yaml_data)
            filter_conf = PremiseFilterConf.from_yaml(yaml_data["premise_filter"])
            return SelectClientConf(
                urls,
                data_conf.context_format_type_alias,
                data_conf.premise_format_type_alias,
                filter_conf,
                data_conf.sentence_db_loc,
            )
        case RerankConf():
            if conf.select_conf is None:
                assert 0 < len(conf.checkpoint_loc.parents)
                model_loc = conf.checkpoint_loc.parents[0]
                data_conf_loc = model_loc / RERANK_DATA_CONF_NAME
                assert data_conf_loc.exists()
                with data_conf_loc.open("r") as fin:
                    yaml_data = yaml.load(fin, Loader=yaml.Loader)
                data_conf = RerankDatasetConf.from_yaml(yaml_data)
                rerank_formatter = start_servers_rerank_formatter_conf(
                    data_conf.rerank_formatter_conf, use_devices
                )
                select_conf = rerank_formatter.select_conf
            else:
                select_conf = start_servers_premise_conf(conf.select_conf, use_devices)
            rerank_urls = start_rerank_servers(conf, use_devices)
            return RerankClientConf(rerank_urls, select_conf, conf.rerank_num)
        case _:
            return conf


def start_servers_formatter_conf(
    conf: FormatterConf, use_devices: list[int]
) -> FormatterConf:
    match conf:
        case PremiseFormatterConf():
            return PremiseFormatterConf(
                start_servers_premise_conf(conf.premise_conf, use_devices),
                conf.n_step_conf,
            )
        case GPTPremiseFormatterConf():
            return GPTPremiseFormatterConf(
                start_servers_premise_conf(conf.premise_conf, use_devices),
            )
        case _:
            return conf


def start_servers_rerank_formatter_conf(
    conf: RerankFormatterConf, use_devices: list[int]
) -> RerankFormatterConf:
    clean_premise_conf = start_servers_premise_conf(conf.select_conf, use_devices)
    return RerankFormatterConf(
        clean_premise_conf, conf.consider_num, conf.negatives_per_positive
    )


def start_servers_lm_dataset_conf(
    conf: LmDatasetConf, use_devices: list[int]
) -> LmDatasetConf:
    lm_confs: list[FormatterConf] = []
    for f in conf.lm_formatter_confs:
        lm_confs.append(start_servers_formatter_conf(f, use_devices))
    return LmDatasetConf(
        conf.n_procs,
        conf.train_sample_loc,
        conf.val_sample_loc,
        conf.test_sample_loc,
        conf.sentence_db_loc,
        conf.output_dataset_loc,
        lm_confs,
    )


def start_tactic_gen_servers(
    conf: FidTacticGenConf, use_devices: list[int]
) -> list[str]:
    global next_port
    urls: list[str] = []
    for device in use_devices:
        env = os.environ | {"CUDA_VISIBLE_DEVICES": f"{device}"}
        command = [
            "python3",
            TACTIC_GEN_SERVER_SCRIPT,
            "fid-local",
            f"{conf.checkpoint_loc}",
            f"{next_port}",
        ]
        process = subprocess.Popen(command, env=env)
        url = f"http://localhost:{next_port}"
        open_servers.append(url)
        urls.append(url)
        next_port += 1
        started_processes.append(process)
    return urls


def start_servers_tactic_gen(
    conf: TacticGenConf, use_devices: list[int]
) -> TacticGenConf:
    match conf:
        case FidTacticGenConf():
            assert conf.checkpoint_loc.exists()
            if conf.formatter_confs is None:
                assert 0 < len(conf.checkpoint_loc.parents)
                model_loc = conf.checkpoint_loc.parents[0]
                lm_data_conf = model_loc / DATA_CONF_NAME
                assert lm_data_conf.exists()
                with lm_data_conf.open("r") as fin:
                    yaml_data = yaml.load(fin, Loader=yaml.Loader)
                data_conf = LmDatasetConf.from_yaml(yaml_data)
                formatter_confs = data_conf.lm_formatter_confs
            else:
                formatter_confs = conf.formatter_confs
            formatter_client_confs = [
                start_servers_formatter_conf(f, use_devices) for f in formatter_confs
            ]
            tactic_urls = start_tactic_gen_servers(conf, use_devices)
            return LocalTacticGenClientConf(tactic_urls, formatter_client_confs)
        case _:
            return conf


def start_servers(conf: TopLevelConf, use_devices: list[int]) -> TopLevelConf:
    """
    Given a configuraion, looks for sub-configurations that
    use a neural model. For each of these, starts a server
    and replaces the sub-configuration with its client.
    """
    match conf:
        case LmDatasetConf():
            return start_servers_lm_dataset_conf(conf, use_devices)
        case TestProofConf():
            tactic_client_conf = start_servers_tactic_gen(conf.tactic_conf, use_devices)
            return TestProofConf(
                conf.theorem_location_info,
                conf.search_conf,
                tactic_client_conf,
                conf.print_proofs,
                conf.print_trees,
            )
        case TestProofsConf():
            tactic_client_conf = start_servers_tactic_gen(conf.tactic_conf, use_devices)
            return TestProofsConf(
                conf.proofs,
                conf.n_procs,
                conf.save_loc,
                conf.data_loc,
                conf.sentence_db_loc,
                conf.data_split_loc,
                conf.search_conf,
                tactic_client_conf,
            )
        case RerankDatasetConf():
            rerank_formatter_conf = start_servers_rerank_formatter_conf(
                conf.rerank_formatter_conf, use_devices
            )
            return RerankDatasetConf(
                conf.n_procs,
                conf.train_sample_loc,
                conf.val_sample_loc,
                conf.test_sample_loc,
                conf.sentence_db_loc,
                conf.output_dataset_loc,
                rerank_formatter_conf,
            )
        case GoalDatasetConf():
            return conf
        case PremiseEvalConf():
            premise_conf = start_servers_premise_conf(conf.premise_conf, use_devices)
            return PremiseEvalConf(
                premise_conf,
                conf.data_loc,
                conf.sentence_db_loc,
                conf.data_split_loc,
                conf.split_name,
                conf.save_loc,
            )
        case TestWholeProofConf():
            tactic_client_conf = start_servers_tactic_gen(conf.tactic_conf, use_devices)
            return TestWholeProofConf(
                conf.theorem_location_info, tactic_client_conf, conf.n_attempts
            )
        case TestWholeProofsConf():
            tactic_client_conf = start_servers_tactic_gen(conf.tactic_conf, use_devices)
            return TestWholeProofsConf(
                conf.proofs,
                conf.n_procs,
                conf.save_loc,
                conf.data_loc,
                conf.sentence_db_loc,
                conf.data_split_loc,
                conf.tactic_conf,
                conf.n_attempts,
            )


@dataclass
class Command:
    conf: type[TopLevelConf]
    py_path: Path


COMMANDS = {
    "prove": Command(TestProofConf, Path("src/model_deployment/run_proof.py")),
    "run-dev": Command(TestProofsConf, Path("src/model_deployment/run_proofs.py")),
    "prove-whole": Command(
        TestWholeProofConf, Path("src/model_deployment/run_whole_proof.py")
    ),
    "run-dev-whole": Command(
        TestWholeProofsConf, Path("src/model_deployment/run_whole_proofs.py")
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


def wait_for_servers():
    print(open_servers)
    for process, server_url in zip(started_processes, open_servers):
        while True:
            try:
                poll_result = subprocess.Popen.poll(process)
                if poll_result is not None:
                    raise ServerFailedError
                response = requests.get(server_url)
                break
            except requests.exceptions.RequestException:
                continue


if __name__ == "__main__":
    command_list = ", ".join(COMMANDS.keys())
    parser = argparse.ArgumentParser()
    parser.add_argument("command", help=f"Select from: {command_list}")
    parser.add_argument("config", help="Yaml configuration file for command.")
    parser.add_argument(
        "devices",
        nargs="+",
        type=int,
        help="CUDA devices to use for running the command.",
    )
    args = parser.parse_args(sys.argv[1:])

    if args.command not in COMMANDS:
        raise (CommandNotFoundError(f"{args.command} not one of {command_list}"))

    command = COMMANDS[args.command]
    config_loc = Path(args.config)
    if not config_loc.exists():
        raise FileNotFoundError(f"{config_loc}")

    with config_loc.open("r") as fin:
        yaml_conf = yaml.load(fin, Loader=yaml.Loader)

    top_level_conf = command.conf.from_yaml(yaml_conf)
    print(top_level_conf)
    clean_conf_path = Path(f"./{CLEAN_CONFIG}")
    try:
        clean_top_level_conf = start_servers(top_level_conf, args.devices)

        with clean_conf_path.open("wb") as fout:
            pickle.dump(clean_top_level_conf, fout)

        print("Waiting for servers to start...")
        wait_for_servers()
        subprocess.run(["python3", command.py_path, args.config])
    finally:
        if clean_conf_path.exists():
            os.remove(clean_conf_path)
        for p in started_processes:
            p.send_signal(signal.SIGINT)
