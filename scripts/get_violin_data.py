import os
import json
from tqdm import tqdm
from pathlib import Path
from dataclasses import dataclass
from data_management.sentence_db import SentenceDB
from data_management.splits import DataSplit, Split
from evaluation.find_coqstoq_idx import get_thm_desc

from coqstoq import Split as CQSplit, get_theorem_list


@dataclass
class CountResult:
    proof_step_count: list[int]
    num_proofs_count: list[int]

    def save(self, steps_loc: Path, proofs_loc: Path):
        with steps_loc.open("w") as f:
            json.dump(self.proof_step_count, f)
        with proofs_loc.open("w") as f:
            json.dump(self.num_proofs_count, f)


def get_training_proof_step_counts(
    split: DataSplit, data_loc: Path, sentence_db: SentenceDB
) -> CountResult:
    proof_step_counts: list[int] = []
    num_proofs_count: dict[str, int] = {}
    for f_info in tqdm(split.get_file_list(Split.TRAIN)):
        proofs = f_info.get_proofs(data_loc, sentence_db)
        for proof in proofs:
            proof_step_counts.append(len(proof.steps))
        if f_info.repository not in num_proofs_count:
            num_proofs_count[f_info.repository] = 0
        num_proofs_count[f_info.repository] += len(proofs)
    return CountResult(proof_step_counts, list(num_proofs_count.values()))


def get_coqstoq_proof_counts(
    coqstoq_loc: Path, coqstoq_split: CQSplit, data_loc: Path, sentence_db: SentenceDB
) -> CountResult:
    coqstoq_thms = get_theorem_list(coqstoq_split, coqstoq_loc)
    proof_step_counts: list[int] = []
    num_proofs_count: dict[str, int] = {}
    for thm in tqdm(coqstoq_thms):
        thm_desc = get_thm_desc(thm, data_loc, sentence_db)
        assert thm_desc is not None
        proof_step_counts.append(len(thm_desc.dp.proofs[thm_desc.idx].steps))
        if thm.project.dir_name not in num_proofs_count:
            num_proofs_count[thm.project.dir_name] = 0
        num_proofs_count[thm.project.dir_name] += 1
    return CountResult(proof_step_counts, list(num_proofs_count.values()))


if __name__ == "__main__":
    SAVE_DIR = Path("data/violin")
    os.makedirs(SAVE_DIR, exist_ok=True)

    # SPLIT_LOC = Path("splits/official-split-icse.json")
    # TRAINING_DATA_LOC = Path("raw-data/coq-dataset")
    # TRAINING_SENTENCE_DB_LOC = Path("raw-data/coq-dataset/sentences.db")

    # training_sdb = SentenceDB.load(TRAINING_SENTENCE_DB_LOC)
    # training_split = DataSplit.load(SPLIT_LOC)

    # training_results = get_training_proof_step_counts(
    #     training_split, TRAINING_DATA_LOC, training_sdb
    # )

    # TRAIN_STEPS_LOC = SAVE_DIR / "train_steps.json"
    # TRAIN_PROOFS_LOC = SAVE_DIR / "train_proofs.json"
    # training_results.save(TRAIN_STEPS_LOC, TRAIN_PROOFS_LOC)

    # COQSTOQ_LOC = Path("/work/pi_brun_umass_edu/kthompson/CoqStoq")
    # COQSTOQ_TEST_LOC = Path("raw-data/coqstoq-test")
    # COQSTOQ_TEST_SDB_LOC = Path("raw-data/coqstoq-test/coqstoq-test-sentences.db")
    # test_sdb = SentenceDB.load(COQSTOQ_TEST_SDB_LOC)
    # test_results = get_coqstoq_proof_counts(
    #     COQSTOQ_LOC, CQSplit.TEST, COQSTOQ_TEST_LOC, test_sdb
    # )
    # TEST_STEPS_LOC = SAVE_DIR / "test_steps.json"
    # TEST_PROOFS_LOC = SAVE_DIR / "test_proofs.json"
    # test_results.save(TEST_STEPS_LOC, TEST_PROOFS_LOC)

    COQSTOQ_LOC = Path("/work/pi_brun_umass_edu/kthompson/CoqStoq")
    COQSTOQ_VAL_LOC = Path("raw-data/coqstoq-val")
    COQSTOQ_VAL_SDB_LOC = Path("raw-data/coqstoq-val/coqstoq-val-sentences.db")
    val_sdb = SentenceDB.load(COQSTOQ_VAL_SDB_LOC)
    test_results = get_coqstoq_proof_counts(
        COQSTOQ_LOC, CQSplit.VAL, COQSTOQ_VAL_LOC, val_sdb
    )

    VAL_STEPS_LOC = SAVE_DIR / "val_steps.json"
    VAL_PROOFS_LOC = SAVE_DIR / "val_proofs.json"
    test_results.save(VAL_STEPS_LOC, VAL_PROOFS_LOC)
