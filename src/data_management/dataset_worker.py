from typing import Optional
import sys, os
import yaml
import argparse
from pathlib import Path
import functools
import jsonlines
import multiprocessing as mp

from data_management.dataset_file import DatasetFile
from data_management.splits import FileInfo
from data_management.sentence_db import SentenceDB
from data_management.dataset_utils import (
    LmDatasetConf,
    SelectDatasetConf,
    RerankDatasetConf,
    DatasetConf,
    DatasetExample,
    data_conf_from_yaml,
)
from tactic_gen.lm_example import (
    FormatterConf,
    LmFormatter,
    formatter_from_conf,
    LmExample,
)
from premise_selection.premise_formatter import PREMISE_ALIASES, CONTEXT_ALIASES
from premise_selection.premise_example import PremiseTrainingExample
from premise_selection.rerank_formatter import (
    RerankFormatterConf,
    RerankFormatter,
    rerank_formatter_from_conf,
)
from premise_selection.rerank_example import RerankExample
from premise_selection.premise_filter import PremiseFilter, PremiseFilterConf
from model_deployment.conf_utils import (
    to_client_conf,
    wait_for_servers,
    start_servers,
    update_ips,
)

from util.file_queue import FileQueue, EmptyFileQueueError
from util.constants import TMP_LOC, PORT_MAP_NAME
from util.util import clear_port_map


@functools.cache
def get_formatter(formatter_conf: FormatterConf) -> LmFormatter:
    return formatter_from_conf(formatter_conf)


def tactic_examples_from_step(
    file_info: FileInfo,
    dataset_conf: LmDatasetConf,
    dset_file: DatasetFile,
    proof_idx: int,
    step_idx: int,
) -> list[LmExample]:
    formatters = [get_formatter(f) for f in dataset_conf.lm_formatter_confs]
    return [
        f.example_from_step(step_idx, proof_idx, dset_file, training=True)
        for f in formatters
    ]


@functools.cache
def get_premise_filter(premise_filter_conf: PremiseFilterConf) -> PremiseFilter:
    return PremiseFilter.from_conf(premise_filter_conf)


def select_examples_from_step(
    dataset_conf: SelectDatasetConf,
    dset_file: DatasetFile,
    proof_idx: int,
    step_idx: int,
) -> list[PremiseTrainingExample]:
    proof = dset_file.proofs[proof_idx]
    step = proof.steps[step_idx]
    premise_format_type = PREMISE_ALIASES[dataset_conf.premise_format_type_alias]
    context_format_type = CONTEXT_ALIASES[dataset_conf.context_format_type_alias]
    filter = get_premise_filter(dataset_conf.premise_filter_conf)
    examples = PremiseTrainingExample.from_focused_step(
        step,
        proof,
        dset_file,
        dataset_conf.num_negatives_per_positive,
        dataset_conf.num_in_file_negatives_per_positive,
        context_format_type,
        premise_format_type,
        filter,
    )
    return examples


@functools.cache
def get_rerank_formatter(conf: RerankFormatterConf) -> RerankFormatter:
    return rerank_formatter_from_conf(conf)


def rerank_examples_from_step(
    dataset_conf: RerankDatasetConf,
    dset_file: DatasetFile,
    proof_idx: int,
    step_idx: int,
) -> list[RerankExample]:
    rerank_formatter = get_rerank_formatter(dataset_conf.rerank_formatter_conf)
    proof = dset_file.proofs[proof_idx]
    step = proof.steps[step_idx]
    return rerank_formatter.examples_from_step(step, proof, dset_file)


def examples_from_file(
    file_info: FileInfo, dataset_conf: DatasetConf, sentence_db: SentenceDB
) -> list[DatasetExample]:
    file_dp = file_info.get_dp(dataset_conf.data_loc, sentence_db)
    examples: list[DatasetExample] = []
    for i, proof in enumerate(file_dp.proofs):
        for j, _ in enumerate(proof.steps):
            match dataset_conf:
                case LmDatasetConf():
                    examples.extend(
                        tactic_examples_from_step(
                            file_info, dataset_conf, file_dp, i, j
                        )
                    )
                case SelectDatasetConf():
                    examples.extend(
                        select_examples_from_step(dataset_conf, file_dp, i, j)
                    )
                case RerankDatasetConf():
                    examples.extend(
                        rerank_examples_from_step(dataset_conf, file_dp, i, j)
                    )
    return examples


def write_examples(
    examples: list[DatasetExample], file_info: FileInfo, dataset_conf: DatasetConf
) -> None:
    out_loc = dataset_conf.output_dataset_loc / file_info.dp_name
    json_examples = [e.to_json() for e in examples]
    assert not out_loc.exists()
    with jsonlines.open(out_loc, "w") as fout:
        fout.write_all(json_examples)


def handle_file(
    file_info: FileInfo, dataset_conf: DatasetConf, sentence_db: SentenceDB
) -> None:
    file_examples = examples_from_file(file_info, dataset_conf, sentence_db)
    write_examples(file_examples, file_info, dataset_conf)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--conf_loc", help="Location of dataset configuration.")
    parser.add_argument("--queue_loc", help="Location of the work queue.")

    args = parser.parse_args(sys.argv[1:])
    dataset_conf_loc = Path(args.conf_loc)
    queue_loc = Path(args.queue_loc)

    assert dataset_conf_loc.exists()
    assert queue_loc.exists()

    with dataset_conf_loc.open("r") as fin:
        yaml_conf = yaml.safe_load(fin)

    dataset_conf = data_conf_from_yaml(yaml_conf)
    clear_port_map()
    dataset_client_conf, num_servers, server_commands = to_client_conf(dataset_conf, 0)
    server_procs = start_servers(server_commands)
    port_map = wait_for_servers(num_servers)
    update_ips(dataset_client_conf, port_map)

    assert isinstance(dataset_client_conf, DatasetConf)
    sentence_db = SentenceDB.load(dataset_client_conf.sentence_db_loc)

    queue: FileQueue = FileQueue(queue_loc)
    while True:
        try:
            file_info = queue.get()
            worker_process = mp.Process(
                target=handle_file, args=(file_info, dataset_client_conf, sentence_db)
            )
            worker_process.start()
            worker_process.join()
        except EmptyFileQueueError:
            break

    for p in server_procs:
        p.kill()
