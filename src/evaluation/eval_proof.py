import sys, os
import argparse
import pickle
from pathlib import Path

from data_management.splits import DataSplit
from data_management.sentence_db import SentenceDB
from evaluation.slurm_eval import ProofMap
from evaluation.evaluate import EvalConf
from model_deployment.mcts_searcher import MCTSConf 
from model_deployment.classical_searcher import ClassicalSearchConf
from model_deployment.prove import LocationInfo, RunProofConf, run_proof, summary_from_result, SearchSummary, MCTSSummary, Summary
from model_deployment.tactic_gen_client import tactic_gen_client_from_conf 

def get_orig_summary(file: Path, theorem: str, eval_conf: EvalConf) -> Summary:
    match eval_conf.search_conf:
        case MCTSConf():
            return MCTSSummary.from_search_result(file, theorem, None)
        case ClassicalSearchConf():
            return SearchSummary.from_search_result(file, theorem, None)


if __name__ == "__main__":
    """This section of the file is just here for evaluation."""
    parser = argparse.ArgumentParser()
    parser.add_argument("pickled_eval_conf_loc")
    parser.add_argument("proof_map_loc")
    parser.add_argument("proof_map_idx", type=int)

    args = parser.parse_args(sys.argv[1:])
    pickled_eval_conf_loc = Path(args.pickled_eval_conf_loc)
    proof_map_loc = Path(args.proof_map_loc)
    proof_map_idx = args.proof_map_idx
    assert isinstance(proof_map_idx, int)

    with pickled_eval_conf_loc.open("rb") as fin:
        eval_conf: EvalConf = pickle.load(fin)

    proof_map = ProofMap.load(proof_map_loc)
    proof_file_info, proof_idx = proof_map.get(proof_map_idx)
    sentence_db = SentenceDB.load(eval_conf.sentence_db_loc)
    proof_dp = proof_file_info.get_dp(eval_conf.data_loc, sentence_db)
    data_split = DataSplit.load(eval_conf.data_split_loc)

    location_info = LocationInfo(
        eval_conf.data_loc, proof_file_info, eval_conf.split, proof_dp, proof_idx, sentence_db, eval
    )
    tactic_client = tactic_gen_client_from_conf(eval_conf.tactic_conf)
    run_conf = RunProofConf(location_info, eval_conf.search_conf, tactic_client, False, False)

    file = eval_conf.data_loc / location_info.file_info.file
    theorem_name = (
        run_conf.location_info.dataset_file.proofs[
            run_conf.location_info.dp_proof_idx
        ].get_theorem_name()
        + "-"
        + str(run_conf.location_info.dp_proof_idx)
    )

    orig_summary = get_orig_summary(file, theorem_name, eval_conf)
    orig_summary.save(eval_conf.save_loc)

    result = run_proof(run_conf) 
    summary = summary_from_result(file, theorem_name, result)
    summary.save(eval_conf.save_loc)

