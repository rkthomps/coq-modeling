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
    CodellamaTacticGenConf,
    LocalTacticGenClientConf,
)
from model_deployment.run_proof import TestProofConf
from model_deployment.run_proofs import TestProofsConf
from model_deployment.run_whole_proof import TestWholeProofConf
from model_deployment.run_whole_proofs import TestWholeProofsConf
from evaluation.evaluate import EvalConf
from util.socket_client import ServerAdapter
from util.constants import (
    PREMISE_DATA_CONF_NAME,
    RERANK_DATA_CONF_NAME,
    DATA_CONF_NAME,
    CLEAN_CONFIG,
    SERVER_LOC,
)


TopLevelConf = (
    LmDatasetConf
    | TestProofConf
    | TestProofsConf
    | TestWholeProofConf
    | TestWholeProofsConf
    | EvalConf
    | SelectDataConfig
    | RerankDatasetConf
    | GoalDatasetConf
    | PremiseEvalConf
)

SELECT_SERVER_SCRIPT = Path("src/model_deployment/select_server.py")
RERANK_SERVER_SCRIPT = Path("src/model_deployment/rerank_server.py")
TACTIC_GEN_SERVER_SCRIPT = Path("src/model_deployment/tactic_gen_server.py")


def __make_select_command(
    select_conf: SelectConf, start_server_num: int
) -> tuple[list[str], int]:
    if select_conf.vector_db_loc is None:
        command = [
            "python3",
            f"{SELECT_SERVER_SCRIPT}",
            f"{select_conf.checkpoint_loc}",
            f"{start_server_num}",
        ]
    else:
        command = [
            "python3",
            f"{SELECT_SERVER_SCRIPT}",
            "--vector_db_loc",
            f"{select_conf.vector_db_loc}",
            f"{select_conf.checkpoint_loc}",
            f"{start_server_num}",
        ]
    return command, start_server_num + 1


def start_select_server(select_conf: SelectConf, start_server_num: int) -> tuple[Path, int, list[str]]:
    command, ret_port = __make_select_command(select_conf, start_server_num)
    server_loc = Path(SERVER_LOC) / str(start_server_num)
    return server_loc, ret_port, command 


def start_rerank_server(rerank_conf: RerankConf, start_server_num: int) -> tuple[Path, int, list[str]]:
    command = [
        "python3",
        f"{RERANK_SERVER_SCRIPT}",
        f"{rerank_conf.checkpoint_loc}",
        f"{start_server_num}",
    ]
    server_loc = Path(SERVER_LOC) / str(start_server_num)
    return server_loc, start_server_num + 1, command 


def start_servers_premise_conf(
    conf: PremiseConf,
    start_server_num: int,
) -> tuple[PremiseConf, int, list[list[str]]]:
    match conf:
        case SelectConf():
            socket_path, next_server_num, command = start_select_server(conf, start_server_num)
            assert 0 < len(conf.checkpoint_loc.parents)
            model_loc = conf.checkpoint_loc.parents[0]
            data_conf_loc = model_loc / PREMISE_DATA_CONF_NAME
            assert data_conf_loc.exists()
            with data_conf_loc.open("r") as fin:
                yaml_data = yaml.load(fin, Loader=yaml.Loader)
            data_conf = SelectDataConfig.from_yaml(yaml_data)
            filter_conf = PremiseFilterConf.from_yaml(yaml_data["premise_filter"])
            new_select_client = SelectClientConf(
                [socket_path],
                data_conf.context_format_type_alias,
                data_conf.premise_format_type_alias,
                filter_conf,
                data_conf.sentence_db_loc,
            )
            return new_select_client, next_server_num, [command]
        case RerankConf():
            if conf.select_conf is None:
                assert 0 < len(conf.checkpoint_loc.parents)
                model_loc = conf.checkpoint_loc.parents[0]
                data_conf_loc = model_loc / RERANK_DATA_CONF_NAME
                assert data_conf_loc.exists()
                with data_conf_loc.open("r") as fin:
                    yaml_data = yaml.load(fin, Loader=yaml.Loader)
                data_conf = RerankDatasetConf.from_yaml(yaml_data)
                rerank_formatter, next_server_num, commands = start_servers_rerank_formatter_conf(
                    data_conf.rerank_formatter_conf, start_server_num 
                )
                select_conf = rerank_formatter.select_conf
            else:
                select_conf, next_server_num, commands = start_servers_premise_conf(conf.select_conf, start_server_num)
            rerank_paths, next_server_num, rerank_command = start_rerank_server(conf, next_server_num)
            new_rerank_conf = RerankClientConf([rerank_paths], select_conf, conf.rerank_num)
            return new_rerank_conf, next_server_num, commands + [rerank_command]
        case _:
            return conf, start_server_num, []


def start_servers_formatter_conf(
    conf: FormatterConf,
    start_server_num: int,
) -> tuple[FormatterConf, int, list[list[str]]]:
    match conf:
        case PremiseFormatterConf():
            premise_conf, next_server_num, commands = start_servers_premise_conf(conf.premise_conf, start_server_num)
            new_premise_formatter = PremiseFormatterConf(premise_conf, conf.n_step_conf)
            return new_premise_formatter, next_server_num, commands
        case GPTPremiseFormatterConf():
            premise_conf, next_server_num, commands = start_servers_premise_conf(conf.premise_conf, start_server_num)
            new_premise_formatter = GPTPremiseFormatterConf(premise_conf)
            return new_premise_formatter, next_server_num, commands
        case _:
            return conf, start_server_num, []


def start_servers_rerank_formatter_conf(
    conf: RerankFormatterConf,
    start_server_num: int,
) -> tuple[RerankFormatterConf, int, list[list[str]]]:
    clean_premise_conf, next_server_num, start_commands = start_servers_premise_conf(conf.select_conf, start_server_num)
    new_rerank_formatter_conf = RerankFormatterConf(
        clean_premise_conf, conf.consider_num, conf.negatives_per_positive
    )
    return new_rerank_formatter_conf, next_server_num, start_commands

def start_servers_lm_dataset_conf(
    conf: LmDatasetConf,
    start_server_num: int,
) -> tuple[LmDatasetConf, int, list[list[str]]]:
    lm_confs: list[FormatterConf] = []
    formatter_commands: list[list[str]] = []
    next_server_num = start_server_num
    for f in conf.lm_formatter_confs:
        formatter_conf, next_server_num, commands = start_servers_formatter_conf(f, next_server_num)
        lm_confs.append(formatter_conf)
        formatter_commands.extend(commands)
    new_dataset_conf = LmDatasetConf(
        conf.n_procs,
        conf.train_sample_loc,
        conf.val_sample_loc,
        conf.test_sample_loc,
        conf.sentence_db_loc,
        conf.output_dataset_loc,
        lm_confs,
    )
    return new_dataset_conf, next_server_num, formatter_commands


def get_tactic_server_alias(conf: FidTacticGenConf | CodellamaTacticGenConf) -> str:
    match conf:
        case FidTacticGenConf():
            return "fid-local"
        case CodellamaTacticGenConf():
            return "local"


def start_tactic_gen_servers(
    conf: FidTacticGenConf | CodellamaTacticGenConf, start_server_num: int
) -> tuple[Path, int, list[str]]:
    command = [
        "python3",
        f"{TACTIC_GEN_SERVER_SCRIPT}",
        get_tactic_server_alias(conf),
        f"{conf.checkpoint_loc}",
        f"{start_server_num}",
    ]
    server_loc = Path(SERVER_LOC) / str(start_server_num)
    return server_loc, start_server_num + 1, command 


def start_servers_tactic_gen(
    conf: TacticGenConf,
    start_server_num: int,
) -> tuple[TacticGenConf, int, list[list[str]]]:
    match conf:
        case FidTacticGenConf() | CodellamaTacticGenConf():
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
            all_commands: list[list[str]] = []
            formatter_confs: list[FormatterConf] = []
            next_server_num = start_server_num
            for f in formatter_confs:
                formatter_client_conf, next_server_num, commands = start_servers_formatter_conf(f, next_server_num)
                all_commands.extend(commands)
                formatter_confs.append(formatter_client_conf)
            tactic_path, next_server_num, tac_command = start_tactic_gen_servers(conf, next_server_num)
            new_tactic_client = LocalTacticGenClientConf([tactic_path], formatter_confs)
            return new_tactic_client, next_server_num, all_commands + [tac_command] 
        case _:
            return conf, start_server_num, []


def start_servers(
    conf: TopLevelConf,
    start_server_num: int,
) -> tuple[TopLevelConf, int, list[list[str]]]:
    """
    Given a configuraion, looks for sub-configurations that
    use a neural model. For each of these, starts a server
    and replaces the sub-configuration with its client.
    """
    match conf:
        case LmDatasetConf():
            return start_servers_lm_dataset_conf(conf, start_server_num)
        case TestProofConf():
            tactic_client_conf, next_server_num, commands = start_servers_tactic_gen(conf.tactic_conf, start_server_num)
            new_proof_conf = TestProofConf(
                conf.theorem_location_info,
                conf.search_conf,
                tactic_client_conf,
                conf.print_proofs,
                conf.print_trees,
            )
            return new_proof_conf, next_server_num, commands 
        case TestProofsConf():
            tactic_client_conf, next_server_num, commands = start_servers_tactic_gen(conf.tactic_conf, start_server_num)
            new_proofs_conf = TestProofsConf(
                conf.proofs,
                conf.n_procs,
                conf.save_loc,
                conf.data_loc,
                conf.sentence_db_loc,
                conf.data_split_loc,
                conf.search_conf,
                tactic_client_conf,
            )
            return new_proofs_conf, next_server_num, commands
        case SelectDataConfig():
            return conf, start_server_num, []
        case RerankDatasetConf():
            rerank_formatter_conf, next_server_num, commands = start_servers_rerank_formatter_conf(
                conf.rerank_formatter_conf, start_server_num 
            )
            reraank_data_conf = RerankDatasetConf(
                conf.n_procs,
                conf.train_sample_loc,
                conf.val_sample_loc,
                conf.test_sample_loc,
                conf.sentence_db_loc,
                conf.output_dataset_loc,
                rerank_formatter_conf,
            )
            return reraank_data_conf, next_server_num, commands
        case GoalDatasetConf():
            return conf, start_server_num, [] 
        case PremiseEvalConf():
            premise_conf, next_server_num, commands = start_servers_premise_conf(conf.premise_conf, start_server_num)
            new_premise_eval_conf = PremiseEvalConf(
                premise_conf,
                conf.data_loc,
                conf.sentence_db_loc,
                conf.data_split_loc,
                conf.split_name,
                conf.save_loc,
            )
            return new_premise_eval_conf, next_server_num, commands
        case TestWholeProofConf():
            tactic_client_conf, next_server_num, commands = start_servers_tactic_gen(conf.tactic_conf, start_server_num)
            new_test_whole_proof_conf = TestWholeProofConf(conf.theorem_location_info, tactic_client_conf, conf.n_attempts)
            return new_test_whole_proof_conf, next_server_num, commands 
        case TestWholeProofsConf():
            tactic_client_conf, next_server_num, commands = start_servers_tactic_gen(conf.tactic_conf, start_server_num)
            new_test_whole_proof_conf = TestWholeProofsConf(
                conf.proofs,
                conf.n_procs,
                conf.save_loc,
                conf.data_loc,
                conf.sentence_db_loc,
                conf.data_split_loc,
                conf.tactic_conf,
                conf.n_attempts,
            )
            return new_test_whole_proof_conf, next_server_num, commands 
        case EvalConf():
            tactic_client_conf, next_server_num, commands = start_servers_tactic_gen(conf.tactic_conf, start_server_num)
            eval_conf = EvalConf(
                conf.n_procs,
                conf.split,
                conf.save_loc,
                conf.data_loc,
                conf.sentence_db_loc,
                conf.data_split_loc,
                conf.search_conf,
                tactic_client_conf,
                conf.max_eval_proofs,
            )
            return eval_conf, next_server_num, commands


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

def merge_two(conf1: TopLevelConf, conf2: TopLevelConf) -> TopLevelConf:
    match conf1:
        case EvalConf():
            assert isinstance(conf2, EvalConf)
            return conf1.merge(conf2)
        case _:
            assert conf1 == conf2
            return conf1


def merge(top_level_confs: list[TopLevelConf]) -> TopLevelConf:
    assert 0 < len(top_level_confs)
    cur_conf = top_level_confs[0]
    for next_conf in top_level_confs[1:]:
        cur_conf = merge_two(cur_conf, next_conf)
    return cur_conf


class CommandNotFoundError(Exception):
    pass


class ServerFailedError(Exception):
    pass


def wait_for_servers(start_server_num: int, next_server_num: int, open_processes: list[subprocess.Popen[bytes]]):
    session = requests.Session()
    urls: list[str] = []
    for num in range(start_server_num, next_server_num):
        url = f"http://servers-{num}/"
        path = Path(SERVER_LOC) / str(num)
        session.mount(f"http://servers-{i}/", ServerAdapter(path))
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
    try:
        next_server_num = 0
        clean_top_level_confs: list[TopLevelConf] = []
        started_processes: list[subprocess.Popen[bytes]] = []
        for d in args.devices:
            clean_top_level_conf, next_server_num, commands = start_servers(top_level_conf, next_server_num)
            clean_top_level_confs.append(clean_top_level_conf)
            env = os.environ | {"CUDA_VISIBLE_DEVICES": f"{d}"}
            for c in commands:
                process = subprocess.Popen(c, env=env)
                started_processes.append(process)

        clean_top_level_conf = merge(clean_top_level_confs)
        with clean_conf_path.open("wb") as fout:
            pickle.dump(clean_top_level_conf, fout)

        print("Waiting for servers to start...")
        wait_for_servers(0, next_server_num, started_processes)
        subprocess.run(["python3", command.py_path, args.config])
    finally:
        if clean_conf_path.exists():
            os.remove(clean_conf_path)
        for p in started_processes:
            p.send_signal(signal.SIGINT)
