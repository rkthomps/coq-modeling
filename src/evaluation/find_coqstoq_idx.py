from dataclasses import dataclass
import argparse
from typing import Optional
from pathlib import Path

from coqstoq import get_theorem_list, Split
from coqstoq.eval_thms import EvalTheorem
from data_management.sentence_db import SentenceDB
from data_management.dataset_file import DatasetFile, DPCache
from data_management.splits import DATA_POINTS_NAME
from data_management.sentence_db import SentenceDB


@dataclass
class ProofLoc:
    dp: DatasetFile
    idx: int


def get_thm_desc(
    thm: EvalTheorem,
    data_loc: Path,
    sentence_db: SentenceDB,
    dp_cache: Optional[DPCache] = None,
) -> Optional[ProofLoc]:
    data_points_loc = data_loc / DATA_POINTS_NAME
    dp_name = str(thm.project.workspace.name / thm.path).replace("/", "-")
    if dp_cache is None:
        dp_loc = data_points_loc / dp_name
        dp = DatasetFile.load(dp_loc, sentence_db, metadata_only=metadata_only)
    else:
        dp = dp_cache.get_dp(dp_name, data_loc, sentence_db)
    for i, proof in enumerate(dp.proofs):
        if proof.theorem.term.line == thm.theorem_start_pos.line:
            if 0 < i:
                assert dp.proofs[i - 1].theorem.term.line < proof.theorem.term.line
            if i + 1 < len(dp.proofs):
                assert proof.theorem.term.line < dp.proofs[i + 1].theorem.term.line
            return ProofLoc(dp, i)
    return None


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("coqstoq_loc")
    parser.add_argument("data_loc")
    parser.add_argument("sentence_db_loc")

    args = parser.parse_args()
    sentence_db = SentenceDB.load(Path(args.sentence_db_loc))

    coqstoq_thms = get_theorem_list(Split.TEST, Path(args.coqstoq_loc))
    for i, thm in enumerate(coqstoq_thms[1:]):
        print(i)
        thm_desc = get_thm_desc(thm, Path(args.data_loc), sentence_db)
        assert thm_desc is not None
