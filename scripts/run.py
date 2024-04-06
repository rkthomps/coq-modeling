import os

import argparse
from subprocess import Popen
from pathlib import Path
import yaml

from data_management.create_lm_dataset import LmDatasetConf
from data_management.create_premise_dataset import SelectDataConfig
from premise_selection.premise_filter import PremiseFilterConf
from tactic_gen.lm_example import (
    FormatterConf,
    PremiseFormatterConf,
)
from model_deployment.premise_client import PremiseConf, SelectConf, SelectClientConf
from model_deployment.tactic_gen_client import TacticGenConf, FidTacticGenConf, TacticGenClientConf 
from util.constants import PREMISE_DATA_CONF_NAME, DATA_CONF_NAME 


TopLevelConf = LmDatasetConf

next_port = 8000
started_processes: list[Popen[bytes]] = []

SELECT_SERVER_SCRIPT = Path("src/model_deployment/select_server.py")
TACTIC_GEN_SERVER_SCRIPT = Path("src/model_deployment/tactic_gen_server.py")


def __make_select_command(select_conf: SelectConf, device: int) -> list[str]:
    if select_conf.vector_db_loc is None:
        command = [
            f"CUDA_VISIBLE_DEVICES={device}",
            "python3",
            f"{SELECT_SERVER_SCRIPT}",
            f"{select_conf.checkpoint_loc}",
            f"{next_port}",
        ]
    else:
        command = [
            f"CUDA_VISIBLE_DEVICES={device}",
            "python3",
            f"SELECT_SERVER_SCRIPT",
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
        command = __make_select_command(select_conf, device)
        process = Popen(command)
        urls.append(f"http//localhost:{next_port}")
        next_port += 1
        started_processes.append(process)
    return urls


def start_servers_premise_formatter_conf(
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
        case _:
            return conf


def start_servers_formatter_conf(
    conf: FormatterConf, use_devices: list[int]
) -> FormatterConf:
    match conf:
        case PremiseFormatterConf():
            return PremiseFormatterConf(
                start_servers_premise_formatter_conf(conf.premise_conf, use_devices),
                conf.n_step_conf,
            )
        case _:
            return conf


def start_servers_lm_dataset_conf(conf: LmDatasetConf, use_devices: list[int]) -> LmDatasetConf:
    lm_conf = start_servers_formatter_conf(conf.lm_formatter_conf, use_devices)
    return LmDatasetConf(
        conf.train_sample_loc,
        conf.val_sample_loc,
        conf.test_sample_loc,
        conf.sentence_db_loc,
        conf.output_dataset_loc,
        lm_conf,
    )

def start_tactic_gen_servers(conf: FidTacticGenConf, use_devices: list[int]) -> list[str]:
    global next_port
    urls: list[str] = []
    for device in use_devices:
        command = [f"CUDA_VISIBLE_DEVICES={device}", "python3", TACTIC_GEN_SERVER_SCRIPT, "local-fid", f"{conf.checkpoint_loc}", f"{next_port}"] 
        process = Popen(command)
        urls.append(f"http//localhost:{next_port}")
        next_port += 1
        started_processes.append(process)
    return urls


def start_servers_tactic_gen(conf: TacticGenConf, use_devices: list[int]) -> TacticGenClientConf:
    match conf:
        case FidTacticGenConf():
            assert 0 < len(conf.checkpoint_loc.parents)
            model_loc = conf.checkpoint_loc.parents[0]
            lm_data_conf = model_loc / DATA_CONF_NAME
            assert lm_data_conf.exists()
            with lm_data_conf.open("r") as fin:
                yaml_data = yaml.load(fin, Loader=yaml.Loader)
            data_conf = LmDatasetConf.from_yaml(yaml_data)
            formatter_conf = data_conf.lm_formatter_conf
            formatter_client_conf = start_servers_formatter_conf(formatter_conf, use_devices)
            tactic_urls = start_tactic_gen_servers(conf, use_devices)
            return TacticGenClientConf(tactic_urls, formatter_client_conf)
        case TacticGenClientConf(): 
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


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
