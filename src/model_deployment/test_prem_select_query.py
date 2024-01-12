from typing import Optional

import requests
import json

from data_management.splits import FileInfo, Split
from data_management.dataset_file import Sentence
from data_management.create_lm_dataset import LmExampleConfig
from tactic_gen.lm_example import BasicFormatter
from model_deployment.premise_model_wrapper import (
    LocalPremiseModelWrapper,
    get_ranked_premise_generator,
)
from model_deployment.searcher import ProofManager

from coqpyt.coq.base_file import CoqFile
from coqpyt.coq.proof_file import ProofFile

from util.util import get_basic_logger

_logger = get_basic_logger(__name__)

# FILE = "/home/ubuntu/coq-modeling/test-coq-projs/min_superlist.v"
# FILE = "/home/ubuntu/coq-modeling/test-coq-projs/min.v"
FILE = "/home/ubuntu/coq-modeling/test-coq-projs/harder_example.v"
N = 20

CHECKPOINT_LOC = "/home/kthompson/coq-modeling/models/prem-select/checkpoint-13683"

premise_model = LocalPremiseModelWrapper.from_checkpoint(CHECKPOINT_LOC)
TEST_FILE = "/home/ubuntu/coq-modeling/examples/Adding/add_2.v"


dummy_file_info = FileInfo(
    "hi-dog",
    TEST_FILE,
    "/home/ubuntu/coq-modeling/examples",
    "/home/ubuntu/coq-modeling/examples",
)
dummy_split = Split.TEST
dummy_data_loc = "/"

with CoqFile(TEST_FILE, workspace=dummy_file_info.workspace) as coq_file:
    print("Initially valid: ", coq_file.is_valid)
    last: Optional[int] = None
    for i, step in enumerate(coq_file.steps):
        if "Theorem" in step.text or "Lemma" in step.text:
            last = i
assert last is not None

dummy_formatter = BasicFormatter()

_logger.debug("Creating Proof File")
with ProofFile(
    TEST_FILE, workspace=dummy_file_info.workspace, timeout=60
) as proof_file:
    proof_point = last
    _logger.debug("Creating Proof Manager")
    with ProofManager(
        TEST_FILE,
        proof_file,
        proof_point,
        dummy_formatter,
        dummy_file_info,
        dummy_split,
        dummy_data_loc,
    ) as proof_manager:
        dset_file = proof_manager.get_dataset_file()
        last_proof = dset_file.proofs[-1]
        last_step = last_proof.steps[-1]

filtered_result = premise_model.premise_filter.get_pos_and_avail_premises(
    last_step, last_proof, dset_file
)

premise_generator = get_ranked_premise_generator(
    premise_model, last_step, last_proof, filtered_result.avail_premises
)

formatted_lines: list[str] = []
for i, premise in enumerate(premise_generator):
    if i >= N:
        break
    assert type(premise) == Sentence
    prefix = "Rec. {:3d}: ".format(i)
    lines = premise.text.split("\n")
    for line in lines:
        formatted_line = f"{prefix}{line} ({premise.sentence_type})"
        formatted_lines.append(formatted_line)
        prefix = " " * len(prefix)
    # formatted_lines.append(f"   File: {premises_before[idx].file_path}:{premises_before[idx].line}")
print("Partial Proof:")
print("---------------")
print(last_proof.proof_prefix_to_string(last_step))
print("\nPremise Recommendations:")
print("-----------------------")
print("\n".join(formatted_lines))
