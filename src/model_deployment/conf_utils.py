from typing import Any, Optional
import os
from pathlib import Path
import yaml
import socket
import functools
from dataclasses import dataclass

from data_management.create_lm_dataset import LmDatasetConf
from data_management.create_rerank_dataset import RerankDatasetConf
from data_management.create_premise_dataset import SelectDataConfig
from data_management.create_goal_dataset import GoalDatasetConf
from premise_selection.premise_filter import PremiseFilterConf
from premise_selection.rerank_formatter import (
    RerankFormatterConf,
    BasicRerankFormatterConf,
    ProofRerankFormatterConf,
)
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
from util.util import get_basic_logger
from util.util import FlexibleUrl
from util.constants import (
    PREMISE_DATA_CONF_NAME,
    RERANK_DATA_CONF_NAME,
    DATA_CONF_NAME,
    CLEAN_CONFIG,
    SERVER_LOC,
    PORT_MAP_LOC,
)

_logger = get_basic_logger(__name__)


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

START_PORT = 19734


@dataclass
class StartTacticModelCommand:
    alias: str
    checkpoint_loc: Path
    port: int
    TACTIC_GEN_SERVER_SCRIPT = Path("src/model_deployment/tactic_gen_server.py")

    def to_list(self) -> list[str]:
        return [
            "python3",
            f"{self.TACTIC_GEN_SERVER_SCRIPT}",
            self.alias,
            f"{self.checkpoint_loc}",
            f"{self.port}",
        ]

    def to_list_slurm(self, env_var_name: str, commands_per_task: int) -> list[str]:
        return [
            "python3",
            f"{self.TACTIC_GEN_SERVER_SCRIPT}",
            self.alias,
            f"{self.checkpoint_loc}",
            f"$(expr ${env_var_name} \\* {commands_per_task} + {self.port})",
        ]


@dataclass
class StartSelectModelCommand:
    vector_db_loc: Optional[Path]
    checkpoint_loc: Path
    port: int
    SELECT_SERVER_SCRIPT = Path("src/model_deployment/select_server.py")

    def to_list(self) -> list[str]:
        if self.vector_db_loc is None:
            return [
                "python3",
                f"{self.SELECT_SERVER_SCRIPT}",
                f"{self.checkpoint_loc}",
                f"{self.port}",
            ]
        return [
            "python3",
            f"{self.SELECT_SERVER_SCRIPT}",
            "--vector_db_loc",
            f"{self.vector_db_loc}",
            f"{self.checkpoint_loc}",
            f"{self.port}",
        ]

    def to_list_slurm(self, env_var_name: str, commands_per_task: int) -> list[str]:
        if self.vector_db_loc is None:
            return [
                "python3",
                f"{self.SELECT_SERVER_SCRIPT}",
                f"{self.checkpoint_loc}",
                f"$(expr ${env_var_name} \\* {commands_per_task} + {self.port})",
            ]
        return [
            "python3",
            f"{self.SELECT_SERVER_SCRIPT}",
            "--vector_db_loc",
            f"{self.vector_db_loc}",
            f"{self.checkpoint_loc}",
            f"$(expr ${env_var_name} \\* {commands_per_task} + {self.port})",
        ]


@dataclass
class StartRerankModelCommand:
    checkpoint_loc: Path
    port: int
    RERANK_SERVER_SCRIPT = Path("src/model_deployment/rerank_server.py")

    def to_list(self) -> list[str]:
        return [
            "python3",
            f"{self.RERANK_SERVER_SCRIPT}",
            f"{self.checkpoint_loc}",
            f"{self.port}",
        ]

    def to_list_slurm(self, env_var_name: str, commands_per_task: int) -> list[str]:
        return [
            "python3",
            f"{self.RERANK_SERVER_SCRIPT}",
            f"{self.checkpoint_loc}",
            f'"expr ${env_var_name} * {commands_per_task} + {self.port}"',
        ]


StartModelCommand = (
    StartTacticModelCommand | StartSelectModelCommand | StartRerankModelCommand
)


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


def clear_port_map():
    port_map_loc = Path(PORT_MAP_LOC)
    if os.path.exists(port_map_loc):
        os.remove(PORT_MAP_LOC)
    with port_map_loc.open("w") as _:
        pass


def read_port_map() -> dict[int, str]:
    port_map_loc = Path(PORT_MAP_LOC)
    port_map: dict[int, str] = {}
    with port_map_loc.open("r") as fin:
        for line in fin:
            lineitems = line.strip().split("\t")
            assert len(lineitems) == 2
            port = int(lineitems[0])
            ip = lineitems[1]
            port_map[port] = ip
    return port_map


def get_flexible_url(ip_addr: str, port: int) -> FlexibleUrl:
    return FlexibleUrl("http", ip_addr, port)


def get_select_command(
    select_conf: SelectConf, start_server_num: int
) -> tuple[FlexibleUrl, int, StartSelectModelCommand]:
    port = START_PORT + start_server_num
    command = StartSelectModelCommand(
        select_conf.vector_db_loc, select_conf.checkpoint_loc, port
    )
    return get_flexible_url(get_ip(), port), start_server_num + 1, command


def get_rerank_command(
    rerank_conf: RerankConf, start_server_num: int
) -> tuple[FlexibleUrl, int, StartRerankModelCommand]:
    port = START_PORT + start_server_num
    command = StartRerankModelCommand(rerank_conf.checkpoint_loc, port)
    return get_flexible_url(get_ip(), port), start_server_num + 1, command


def premise_conf_to_client_conf(
    conf: PremiseConf,
    start_server_num: int,
) -> tuple[PremiseConf, int, list[StartModelCommand]]:
    match conf:
        case SelectConf():
            url, next_server_num, command = get_select_command(conf, start_server_num)
            assert 0 < len(conf.checkpoint_loc.parents)
            model_loc = conf.checkpoint_loc.parents[0]
            data_conf_loc = model_loc / PREMISE_DATA_CONF_NAME
            assert data_conf_loc.exists()
            with data_conf_loc.open("r") as fin:
                yaml_data = yaml.load(fin, Loader=yaml.Loader)
            data_conf = SelectDataConfig.from_yaml(yaml_data)
            filter_conf = PremiseFilterConf.from_yaml(yaml_data["premise_filter"])
            new_select_client = SelectClientConf(
                [url],
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
                rerank_formatter, next_server_num, commands = (
                    rerank_formatter_conf_to_client_conf(
                        data_conf.rerank_formatter_conf, start_server_num
                    )
                )
                select_conf = rerank_formatter.select_conf
            else:
                select_conf, next_server_num, commands = premise_conf_to_client_conf(
                    conf.select_conf, start_server_num
                )
            rerank_url, next_server_num, rerank_command = get_rerank_command(
                conf, next_server_num
            )
            new_rerank_conf = RerankClientConf(
                [rerank_url], select_conf, conf.rerank_num
            )
            return new_rerank_conf, next_server_num, commands + [rerank_command]
        case _:
            return conf, start_server_num, []


def formatter_conf_to_client_conf(
    conf: FormatterConf,
    start_server_num: int,
) -> tuple[FormatterConf, int, list[StartModelCommand]]:
    match conf:
        case PremiseFormatterConf():
            premise_conf, next_server_num, commands = premise_conf_to_client_conf(
                conf.premise_conf, start_server_num
            )
            new_premise_formatter = PremiseFormatterConf(premise_conf, conf.n_step_conf)
            return new_premise_formatter, next_server_num, commands
        case GPTPremiseFormatterConf():
            premise_conf, next_server_num, commands = premise_conf_to_client_conf(
                conf.premise_conf, start_server_num
            )
            new_premise_formatter = GPTPremiseFormatterConf(premise_conf)
            return new_premise_formatter, next_server_num, commands
        case _:
            return conf, start_server_num, []


def rerank_formatter_conf_to_client_conf(
    conf: RerankFormatterConf,
    start_server_num: int,
) -> tuple[RerankFormatterConf, int, list[StartModelCommand]]:
    clean_premise_conf, next_server_num, start_commands = premise_conf_to_client_conf(
        conf.select_conf, start_server_num
    )
    match conf:
        case BasicRerankFormatterConf():
            new_rerank_formatter_conf = BasicRerankFormatterConf(
                clean_premise_conf, conf.consider_num, conf.negatives_per_positive
            )
        case ProofRerankFormatterConf():
            new_rerank_formatter_conf = ProofRerankFormatterConf(
                clean_premise_conf,
                conf.proof_retriever,
                conf.consider_num,
                conf.include_proofs_num,
                conf.negatives_per_positive,
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


def get_tactic_gen_command(
    conf: FidTacticGenConf | CodellamaTacticGenConf, start_server_num: int
) -> tuple[FlexibleUrl, int, StartTacticModelCommand]:
    port = START_PORT + start_server_num
    command = StartTacticModelCommand(
        get_tactic_server_alias(conf), conf.checkpoint_loc, port
    )
    return get_flexible_url(get_ip(), port), start_server_num + 1, command


def tactic_gen_to_client_conf(
    conf: TacticGenConf,
    start_server_num: int,
) -> tuple[TacticGenConf, int, list[StartModelCommand]]:
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


def update_ips(conf: TopLevelConf, port_map: dict[int, str]):
    match conf:
        case EvalConf():
            conf.update_ips(port_map)
        case _:
            _logger.warning(
                "IP updating only implemented for evaluation. Inter-node communication might not work."
            )  # TODO


def to_client_conf(
    conf: TopLevelConf,
    start_server_num: int,
) -> tuple[TopLevelConf, int, list[StartModelCommand]]:
    """
    Given a configuraion, looks for sub-configurations that
    use a neural model. For each of these, starts a server
    and replaces the sub-configuration with its client.
    """
    match conf:
        case LmDatasetConf():
            return lm_dataset_conf_to_client_conf(conf, start_server_num)
        case TestProofConf():
            tactic_client_conf, next_server_num, commands = tactic_gen_to_client_conf(
                conf.tactic_conf, start_server_num
            )
            new_proof_conf = TestProofConf(
                conf.theorem_location_info,
                conf.search_conf,
                tactic_client_conf,
                conf.print_proofs,
                conf.print_trees,
            )
            return new_proof_conf, next_server_num, commands
        case TestProofsConf():
            tactic_client_conf, next_server_num, commands = tactic_gen_to_client_conf(
                conf.tactic_conf, start_server_num
            )
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
            rerank_formatter_conf, next_server_num, commands = (
                rerank_formatter_conf_to_client_conf(
                    conf.rerank_formatter_conf, start_server_num
                )
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
            premise_conf, next_server_num, commands = premise_conf_to_client_conf(
                conf.premise_conf, start_server_num
            )
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
            tactic_client_conf, next_server_num, commands = tactic_gen_to_client_conf(
                conf.tactic_conf, start_server_num
            )
            new_test_whole_proof_conf = TestWholeProofConf(
                conf.theorem_location_info, tactic_client_conf, conf.n_attempts
            )
            return new_test_whole_proof_conf, next_server_num, commands
        case TestWholeProofsConf():
            tactic_client_conf, next_server_num, commands = tactic_gen_to_client_conf(
                conf.tactic_conf, start_server_num
            )
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
            tactic_client_conf, next_server_num, commands = tactic_gen_to_client_conf(
                conf.tactic_conf, start_server_num
            )
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
