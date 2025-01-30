import argparse
import os
import time
import json
import yaml
from pathlib import Path
from coqstoq import get_theorem_list
from coqstoq.eval_thms import EvalTheorem

from data_management.sentence_db import SentenceDB

from evaluation.eval_utils import EvalConf
from evaluation.find_coqstoq_idx import get_thm_desc
from model_deployment.tactic_gen_client import (
    OpenAIClientConf,
    tactic_gen_client_from_conf,
)
from model_deployment.whole_proof_searcher import (
    WholeProofSearcherConf,
    WholeProofSuccess,
    WholeProofFailure,
)
from model_deployment.prove import LocationInfo, RunProofConf, get_save_loc, run_proof
from util.coqstoq_utils import get_file_loc, get_workspace_loc


def get_thms(conf: EvalConf) -> list[EvalTheorem]:
    thm_list = get_theorem_list(conf.split, conf.coqstoq_loc)
    if conf.proof_ids is not None:
        return [thm_list[id] for id in conf.proof_ids]
    else:
        return thm_list


def run_gpt_proof(
    thm: EvalTheorem, run_conf: RunProofConf, save_dir: Path
) -> WholeProofSuccess | WholeProofFailure:
    save_loc = get_save_loc(save_dir, thm)
    result = run_proof(run_conf)
    assert isinstance(result, WholeProofSuccess) or isinstance(
        result, WholeProofFailure
    )
    os.makedirs(save_loc.parent, exist_ok=True)
    with open(save_loc, "w") as fout:
        json.dump(result.to_json(), fout)
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--conf_loc", type=str, required=True)
    args = parser.parse_args()

    with open(args.conf_loc, "r") as fin:
        yaml_data = yaml.safe_load(fin)
    conf = EvalConf.from_yaml(yaml_data)

    assert len(conf.tactic_confs) == 1
    tactic_conf = conf.tactic_confs[0]
    assert isinstance(tactic_conf, OpenAIClientConf)
    assert isinstance(conf.search_conf, WholeProofSearcherConf)
    tactic_client = tactic_gen_client_from_conf(tactic_conf)

    thms = get_thms(conf)
    sentence_db = SentenceDB.load(conf.sentence_db_loc)

    for thm in thms:
        thm_desc = get_thm_desc(thm, conf.data_loc, sentence_db)

        if thm_desc is None:
            raise ValueError(f"Could not find {thm.path} in {conf.data_loc}")

        assert thm_desc is not None

        proof_dp = thm_desc.dp

        location_info = LocationInfo(
            conf.data_loc,
            get_file_loc(thm, conf.coqstoq_loc),
            get_workspace_loc(thm, conf.coqstoq_loc),
            proof_dp,
            thm_desc.idx,
            sentence_db,
        )
        run_conf = RunProofConf(
            location_info, conf.search_conf, [tactic_client], False, False
        )

        save_loc = get_save_loc(conf.save_loc, thm)
        if save_loc.exists():
            print(f"Skipping {thm.path}::{run_conf.theorem_id}")
            continue

        run_gpt_proof(thm, run_conf, conf.save_loc)
