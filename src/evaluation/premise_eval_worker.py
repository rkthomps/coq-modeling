import sys, os
import pickle
import argparse
from pathlib import Path
import multiprocessing as mp

from data_management.dataset_file import DatasetFile
from data_management.splits import FileInfo
from data_management.sentence_db import SentenceDB
from model_deployment.rerank_client import (
    PremiseConf,
    PremiseClient,
    premise_client_from_conf,
)
from evaluation.eval_utils import PremiseEvalConf, PremiseProofResult, PremiseStepResult
from util.file_queue import FileQueue, EmptyFileQueueError


def eval_step_premises(
    premise_client: PremiseClient, proof_dp: DatasetFile, proof_idx: int, step_idx: int
) -> PremiseStepResult:
    proof = proof_dp.proofs[proof_idx]
    step = proof.steps[step_idx]
    filter_result = premise_client.premise_filter.get_pos_and_avail_premises(
        step, proof, proof_dp
    )
    if len(filter_result.pos_premises) == 0:
        return PremiseStepResult(step_idx, 0, [])
    ranked_premise_generator = premise_client.get_ranked_premise_generator(
        step, proof, proof_dp, filter_result.avail_premises
    )
    hits_on: list[int] = []
    num_pos_premises = len(filter_result.pos_premises)
    premises_to_cover = filter_result.pos_premises.copy()
    for i, premise_rec in enumerate(ranked_premise_generator):
        if premise_rec in premises_to_cover:
            premises_to_cover.remove(premise_rec)
            hits_on.append(i + 1)
            if len(premises_to_cover) == 0:
                break
    return PremiseStepResult(step_idx, num_pos_premises, hits_on)


def eval_proof_premises(
    save_loc: Path,
    file: str,
    premise_client_conf: PremiseConf,
    proof_dp: DatasetFile,
    proof_idx: int,
):
    premise_client = premise_client_from_conf(premise_client_conf)
    proof = proof_dp.proofs[proof_idx]
    step_results: list[PremiseStepResult] = []
    for i, step in enumerate(proof.steps):
        step_result = eval_step_premises(premise_client, proof_dp, proof_idx, i)
        step_results.append(step_result)
    proof_result = PremiseProofResult(file, proof_idx, step_results)
    proof_result.save(save_loc)


if __name__ == "__main__":
    parser = argparse.ArgumentParser("Worker for premise evaluation.")
    parser.add_argument("premise_eval_pkl_conf_loc")
    parser.add_argument("premise_eval_queue_loc")

    args = parser.parse_args(sys.argv[1:])
    eval_pkl_conf_loc = Path(args.eval_pkl_conf_loc)
    queue_loc = Path(args.queue_loc)
    assert eval_pkl_conf_loc.exists()
    assert queue_loc.exists()
    q = FileQueue[tuple[FileInfo, int]](queue_loc)

    with eval_pkl_conf_loc.open("rb") as fin:
        eval_conf: PremiseEvalConf = pickle.load(fin)

    sentence_db = SentenceDB.load(eval_conf.sentence_db_loc)

    while True:
        try:
            file_info, idx = q.get()
        except EmptyFileQueueError:
            break

        proof_dp = file_info.get_dp(eval_conf.data_loc, sentence_db)
        worker_process = mp.Process(
            target=eval_proof_premises,
            args=(
                eval_conf.save_loc,
                file_info.file,
                eval_conf.premise_conf,
                proof_dp,
                idx,
            ),
        )
