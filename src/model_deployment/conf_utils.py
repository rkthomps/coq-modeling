from typing import Any, Optional
import time
import os
import socket
import requests
import subprocess
from pathlib import Path
import yaml
import socket
import functools
from dataclasses import dataclass

from data_management.dataset_utils import (
    LmDatasetConf,
    LemmaDatasetConf,
    SelectDatasetConf,
    RerankDatasetConf,
)
from premise_selection.premise_filter import PremiseFilterConf
from premise_selection.rerank_formatter import (
    RerankFormatterConf,
    BasicRerankFormatterConf,
)

from proof_retrieval.proof_retriever import (
    ProofRetrieverConf,
    DeepProofRetrieverClientConf,
    DeepProofRetrieverConf,
)

from lemma_gen.lemma_example import LemmaFormatterConf

from tactic_gen.lm_example import (
    FormatterConf,
    GeneralFormatterConf,
    formatter_conf_from_yaml,
    formatter_update_ips,
)
from premise_selection.rerank_client import (
    PremiseConf,
    SelectClientConf,
    SelectModelClientConf,
    RerankConf,
    RerankClientConf,
    premise_conf_update_ips,
)
from premise_selection.premise_client import SelectModelClientConf, SelectModelConf
from model_deployment.tactic_gen_client import (
    TacticGenConf,
    FidTacticGenConf,
    DecoderTacticGenConf,
    LocalTacticGenClientConf,
)
from evaluation.eval_utils import EvalConf, PremiseEvalConf
from util.util import get_basic_logger, read_port_map
from util.util import FlexibleUrl, get_flexible_url
from util.constants import (
    PREMISE_DATA_CONF_NAME,
    RERANK_DATA_CONF_NAME,
    DATA_CONF_NAME,
    TRAINING_CONF_NAME,
    CLEAN_CONFIG,
    SERVER_LOC,
)

_logger = get_basic_logger(__name__)


@dataclass
class StartTacticModelCommand:
    alias: str
    checkpoint_loc: Path
    id: int
    TACTIC_GEN_SERVER_SCRIPT = Path("src/model_deployment/tactic_gen_server.py")

    def to_list(self) -> list[str]:
        return [
            "python3",
            f"{self.TACTIC_GEN_SERVER_SCRIPT}",
            self.alias,
            f"{self.checkpoint_loc}",
            f"{self.id}",
            f"{os.getpid()}",
        ]

    def to_list_slurm(self, env_var_name: str, commands_per_task: int) -> list[str]:
        return [
            "LOG_LEVEL=DEBUG",
            "python3",
            f"{self.TACTIC_GEN_SERVER_SCRIPT}",
            self.alias,
            f"{self.checkpoint_loc}",
            f"$(expr ${env_var_name} \\* {commands_per_task} + {self.id})",
            f"{os.getpid()}",
        ]


@dataclass
class StartSelectModelCommand:
    vector_db_loc: Optional[Path]
    checkpoint_loc: Path
    id: int
    SELECT_SERVER_SCRIPT = Path("src/model_deployment/select_server.py")

    def to_list(self) -> list[str]:
        if self.vector_db_loc is None:
            return [
                "python3",
                f"{self.SELECT_SERVER_SCRIPT}",
                f"{self.checkpoint_loc}",
                f"{self.id}",
                f"{os.getpid()}",
            ]
        return [
            "python3",
            f"{self.SELECT_SERVER_SCRIPT}",
            "--vector_db_loc",
            f"{self.vector_db_loc}",
            f"{self.checkpoint_loc}",
            f"{self.id}",
            f"{os.getpid()}",
        ]

    def to_list_slurm(self, env_var_name: str, commands_per_task: int) -> list[str]:
        if self.vector_db_loc is None:
            return [
                "LOG_LEVEL=DEBUG",
                "python3",
                f"{self.SELECT_SERVER_SCRIPT}",
                f"{self.checkpoint_loc}",
                f"$(expr ${env_var_name} \\* {commands_per_task} + {self.id})",
                f"{os.getpid()}",
            ]
        return [
            "LOG_LEVEL=DEBUG",
            "python3",
            f"{self.SELECT_SERVER_SCRIPT}",
            "--vector_db_loc",
            f"{self.vector_db_loc}",
            f"{self.checkpoint_loc}",
            f"$(expr ${env_var_name} \\* {commands_per_task} + {self.id})",
            f"{os.getpid()}",
        ]


@dataclass
class StartRerankModelCommand:
    checkpoint_loc: Path
    id: int
    RERANK_SERVER_SCRIPT = Path("src/premise_selection/rerank_server.py")

    def to_list(self) -> list[str]:
        return [
            "python3",
            f"{self.RERANK_SERVER_SCRIPT}",
            f"{self.checkpoint_loc}",
            f"{self.id}",
            f"{os.getpid()}",
        ]

    def to_list_slurm(self, env_var_name: str, commands_per_task: int) -> list[str]:
        return [
            "LOG_LEVEL=DEBUG",
            "python3",
            f"{self.RERANK_SERVER_SCRIPT}",
            f"{self.checkpoint_loc}",
            f"$(expr ${env_var_name} \\* {commands_per_task} + {self.id})",
            f"{os.getpid()}",
        ]


@dataclass
class StartProofModelCommand:
    model_name: str | Path
    vector_db_loc: Path
    max_seq_len: int
    id: int
    PROOF_SERVER_SCRIPT = Path("src/proof_retrieval/proof_ret_server.py")

    def to_list(self) -> list[str]:
        return [
            "python3",
            f"{self.PROOF_SERVER_SCRIPT}",
            f"{self.model_name}",
            f"{self.max_seq_len}",
            f"{self.vector_db_loc}",
            f"{self.id}",
            f"{os.getpid()}",
        ]

    def to_list_slurm(self, env_var_name: str, commands_per_task: int) -> list[str]:
        return [
            "LOG_LEVEL=DEBUG",
            "python3",
            f"{self.PROOF_SERVER_SCRIPT}",
            f"{self.model_name}",
            f"{self.max_seq_len}",
            f"{self.vector_db_loc}",
            f"$(expr ${env_var_name} \\* {commands_per_task} + {self.id})",
            f"{os.getpid()}",
        ]


StartModelCommand = (
    StartTacticModelCommand
    | StartSelectModelCommand
    | StartRerankModelCommand
    | StartProofModelCommand
)


def get_free_port():
    sock = socket.socket()
    sock.bind(("", 0))
    return sock.getsockname()[1]


@functools.cache
def get_ip():
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    s.settimeout(0)
    try:
        # doesn't even have to be reachable
        s.connect(("10.254.254.254", 1))
        ip = s.getsockname()[0]
    except Exception:
        ip = "127.0.0.1"
    finally:
        s.close()
    return ip


def get_select_command(
    select_conf: SelectModelConf, start_server_num: int
) -> tuple[FlexibleUrl, int, StartSelectModelCommand]:
    command = StartSelectModelCommand(
        select_conf.vector_db_loc, select_conf.checkpoint_loc, start_server_num
    )
    return get_flexible_url(start_server_num, get_ip()), start_server_num + 1, command


def get_rerank_command(
    rerank_conf: RerankConf, start_server_num: int
) -> tuple[FlexibleUrl, int, StartRerankModelCommand]:
    command = StartRerankModelCommand(rerank_conf.checkpoint_loc, start_server_num)
    return get_flexible_url(start_server_num, get_ip()), start_server_num + 1, command


def proof_conf_to_client_conf(
    conf: ProofRetrieverConf, start_server_num: int
) -> tuple[ProofRetrieverConf, int, list[StartModelCommand]]:
    match conf:
        case DeepProofRetrieverConf():
            command = StartProofModelCommand(
                conf.model_name, conf.vector_db_loc, conf.max_seq_len, start_server_num
            )
            flex_url = get_flexible_url(start_server_num, get_ip())
            new_retriever_client = DeepProofRetrieverClientConf(
                [flex_url],
                conf.vector_db_loc,
                conf.sentence_db_loc,
                conf.data_loc,
                conf.max_num_proofs,
                conf.first_step_only,
            )
            return new_retriever_client, start_server_num + 1, [command]
        case _:
            return conf, start_server_num, []


def premise_conf_to_client_conf(
    conf: PremiseConf,
    start_server_num: int,
) -> tuple[PremiseConf, int, list[StartModelCommand]]:
    match conf:
        case SelectModelConf():
            url, next_server_num, command = get_select_command(conf, start_server_num)
            assert 0 < len(conf.checkpoint_loc.parents)
            model_loc = conf.checkpoint_loc.parents[0]
            data_conf_loc = model_loc / PREMISE_DATA_CONF_NAME
            assert data_conf_loc.exists()
            with data_conf_loc.open("r") as fin:
                yaml_data = yaml.load(fin, Loader=yaml.Loader)
            data_conf = SelectDatasetConf.from_yaml(yaml_data)
            filter_conf = PremiseFilterConf.from_yaml(yaml_data["premise_filter"])
            new_select_client = SelectModelClientConf(
                [url],
                data_conf.context_format_type_alias,
                data_conf.premise_format_type_alias,
                filter_conf,
                data_conf.sentence_db_loc,
                conf.cached_premise_loc,
            )
            return new_select_client, next_server_num, [command]
        case RerankConf():
            assert 0 < len(conf.checkpoint_loc.parents)
            model_loc = conf.checkpoint_loc.parents[0]
            data_conf_loc = model_loc / RERANK_DATA_CONF_NAME
            assert data_conf_loc.exists()
            with data_conf_loc.open("r") as fin:
                yaml_data = yaml.load(fin, Loader=yaml.Loader)
            data_conf = RerankDatasetConf.from_yaml(yaml_data)
            rerank_formatter, next_server_num, commands = (
                rerank_formatter_conf_to_client_conf(
                    data_conf.rerank_formatter_conf, start_server_num
                )
            )
            select_conf = rerank_formatter.select_conf

            rerank_url, next_server_num, rerank_command = get_rerank_command(
                conf, next_server_num
            )
            new_rerank_conf = RerankClientConf(
                [rerank_url], select_conf, conf.rerank_num, rerank_formatter
            )
            return new_rerank_conf, next_server_num, commands + [rerank_command]
        case _:
            return conf, start_server_num, []


def formatter_conf_to_client_conf(
    conf: FormatterConf,
    start_server_num: int,
) -> tuple[FormatterConf, int, list[StartModelCommand]]:
    match conf:
        case GeneralFormatterConf():
            next_server_num = start_server_num
            if conf.premise_client_conf is not None:
                new_premise_conf, next_server_num, premise_commands = (
                    premise_conf_to_client_conf(
                        conf.premise_client_conf, next_server_num
                    )
                )
            else:
                new_premise_conf = conf.premise_client_conf
                premise_commands = []

            if conf.proof_retriever_conf is not None:
                new_proof_ret_conf, next_server_num, proof_ret_commands = (
                    proof_conf_to_client_conf(
                        conf.proof_retriever_conf, next_server_num
                    )
                )
            else:
                new_proof_ret_conf = conf.proof_retriever_conf
                proof_ret_commands = []

            new_general_formatter = GeneralFormatterConf(
                new_premise_conf,
                new_proof_ret_conf,
                conf.num_premises,
                conf.num_proofs,
            )
            return (
                new_general_formatter,
                next_server_num,
                premise_commands + proof_ret_commands,
            )


def lemma_formatter_conf_to_client_conf(
    conf: LemmaFormatterConf, start_server_num: int
) -> tuple[LemmaFormatterConf, int, list[StartModelCommand]]:
    if conf.premise_conf is None:
        return conf, start_server_num, []
    premise_conf, next_num, commands = premise_conf_to_client_conf(
        conf.premise_conf, start_server_num
    )
    new_conf = LemmaFormatterConf(
        conf.premise_filter_conf, premise_conf, conf.max_num_premises
    )
    return (
        new_conf,
        next_num,
        commands,
    )


def rerank_formatter_conf_to_client_conf(
    conf: RerankFormatterConf,
    start_server_num: int,
) -> tuple[RerankFormatterConf, int, list[StartModelCommand]]:
    clean_premise_conf, next_server_num, start_commands = premise_conf_to_client_conf(
        conf.select_conf, start_server_num
    )
    assert isinstance(clean_premise_conf, SelectClientConf)
    match conf:
        case BasicRerankFormatterConf():
            new_rerank_formatter_conf = BasicRerankFormatterConf(
                clean_premise_conf, conf.consider_num, conf.negatives_per_positive
            )
    return new_rerank_formatter_conf, next_server_num, start_commands


def lm_dataset_conf_to_client_conf(
    conf: LmDatasetConf,
    start_server_num: int,
) -> tuple[LmDatasetConf, int, list[StartModelCommand]]:
    lm_confs: list[FormatterConf] = []
    formatter_commands: list[StartModelCommand] = []
    next_server_num = start_server_num
    for f in conf.lm_formatter_confs:
        formatter_conf, next_server_num, commands = formatter_conf_to_client_conf(
            f, next_server_num
        )
        lm_confs.append(formatter_conf)
        formatter_commands.extend(commands)
    new_dataset_conf = LmDatasetConf(
        conf.data_split_locs,
        conf.data_loc,
        conf.sentence_db_loc,
        conf.output_dataset_loc,
        lm_confs,
    )
    return new_dataset_conf, next_server_num, formatter_commands


def lemma_dataset_conf_to_client_conf(
    conf: LemmaDatasetConf, start_server_num: int
) -> tuple[LemmaDatasetConf, int, list[StartModelCommand]]:
    formatter_conf, next_server_num, commands = lemma_formatter_conf_to_client_conf(
        conf.lemma_formatter_conf, start_server_num
    )
    return (
        LemmaDatasetConf(
            conf.data_split_locs,
            conf.data_loc,
            conf.sentence_db_loc,
            conf.output_dataset_loc,
            formatter_conf,
        ),
        next_server_num,
        commands,
    )


def rerank_dataset_conf_to_client_conf(
    conf: RerankDatasetConf,
    start_server_num: int,
) -> tuple[RerankDatasetConf, int, list[StartModelCommand]]:
    rerank_formatter, next_server_num, commands = rerank_formatter_conf_to_client_conf(
        conf.rerank_formatter_conf, start_server_num
    )
    new_rerank_conf = RerankDatasetConf(
        conf.data_split_locs,
        conf.data_loc,
        conf.sentence_db_loc,
        conf.output_dataset_loc,
        rerank_formatter,
    )
    return new_rerank_conf, next_server_num, commands


def start_servers(commands: list[StartModelCommand]) -> list[subprocess.Popen[bytes]]:
    procs: list[subprocess.Popen[bytes]] = []
    for command in commands:
        p = subprocess.Popen(command.to_list())
        procs.append(p)
    return procs


def wait_for_servers(next_server_num: int) -> dict[int, tuple[str, int]]:
    """Returns a map of port -> ip addr"""
    session = requests.Session()
    urls: list[str] = []

    cur_port_map = read_port_map()
    total_time_slept = 0
    while len(cur_port_map) < next_server_num:
        if 1 < total_time_slept and total_time_slept % 10 == 0:
            _logger.info(
                f"Port map of length {len(cur_port_map)} not complete after {total_time_slept}."
            )
        time.sleep(1)
        total_time_slept += 1
        cur_port_map = read_port_map()

    for port_incr in range(next_server_num):
        ip_addr, port = cur_port_map[port_incr]
        url = get_flexible_url(port_incr, ip_addr, port).get_url()
        urls.append(url)

    _logger.info("Waiting for urls: " + str(urls))
    for server_url in urls:
        while True:
            try:
                session.get(server_url)
                break
            except requests.exceptions.RequestException:
                continue
    return cur_port_map


def get_tactic_server_alias(conf: FidTacticGenConf | DecoderTacticGenConf) -> str:
    match conf:
        case FidTacticGenConf():
            return "fid-local"
        case DecoderTacticGenConf():
            return "decoder-local"


def get_tactic_gen_command(
    conf: FidTacticGenConf | DecoderTacticGenConf, start_server_num: int
) -> tuple[FlexibleUrl, int, StartTacticModelCommand]:
    command = StartTacticModelCommand(
        get_tactic_server_alias(conf), conf.checkpoint_loc, start_server_num
    )
    return get_flexible_url(start_server_num, get_ip()), start_server_num + 1, command


def tactic_gen_to_client_conf(
    conf: TacticGenConf,
    start_server_num: int,
) -> tuple[TacticGenConf, int, list[StartModelCommand]]:
    match conf:
        case FidTacticGenConf() | DecoderTacticGenConf():
            assert conf.checkpoint_loc.exists()
            if conf.formatter_confs is None:
                assert 0 < len(conf.checkpoint_loc.parents)
                model_loc = conf.checkpoint_loc.parents[0]
                lm_data_conf = model_loc / DATA_CONF_NAME
                if lm_data_conf.exists():
                    with lm_data_conf.open("r") as fin:
                        yaml_data = yaml.load(fin, Loader=yaml.Loader)
                    data_conf = LmDatasetConf.from_yaml(yaml_data)
                    formatter_confs = data_conf.lm_formatter_confs
                else:
                    train_conf_loc = model_loc / TRAINING_CONF_NAME
                    assert train_conf_loc.exists()
                    with train_conf_loc.open("r") as fin:
                        yaml_data = yaml.load(fin, Loader=yaml.Loader)
                    formatter_conf = formatter_conf_from_yaml(
                        yaml_data["tactic_data"]["formatter_conf"]
                    )
                    formatter_confs = [formatter_conf]
            else:
                formatter_confs = conf.formatter_confs
            all_commands: list[StartModelCommand] = []
            all_formatter_confs: list[FormatterConf] = []
            next_server_num = start_server_num
            for f in formatter_confs:
                formatter_client_conf, next_server_num, commands = (
                    formatter_conf_to_client_conf(f, next_server_num)
                )
                all_commands.extend(commands)
                all_formatter_confs.append(formatter_client_conf)
            url, next_server_num, tac_command = get_tactic_gen_command(
                conf, next_server_num
            )
            new_tactic_client = LocalTacticGenClientConf([url], all_formatter_confs)
            return new_tactic_client, next_server_num, all_commands + [tac_command]
        case _:
            return conf, start_server_num, []
