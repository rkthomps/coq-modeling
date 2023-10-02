

import requests
import json

from premise_selection.premise_filter import PremiseFilter, FilteredResult
from data_management.dataset_file import Sentence
from data_management.create_lm_dataset import LmExampleConfig
from tactic_gen.lm_example import BasicLmExample
from model_deployment.premise_model_wrapper import PremiseServerModelWrapper
from model_deployment.searcher import ProofManager

URL = "http://127.0.0.1:5000"
#FILE = "/home/ubuntu/coq-modeling/test-coq-projs/min_superlist.v"
#FILE = "/home/ubuntu/coq-modeling/test-coq-projs/min.v"
FILE = "/home/ubuntu/coq-modeling/test-coq-projs/harder_example.v"
N = 20

premise_server = PremiseServerModelWrapper.from_url(URL)
void_lm_config = LmExampleConfig.void_config()

# TODO: ACCESS context through proof manager to get premise selection ex.
with ProofManager(FILE, void_lm_config) as pm:
    dset_obj = pm.get_dataset_file("")
    last_proof = dset_obj.proofs[-1]
    last_step = last_proof.steps[-1]

filtered_result = premise_server.premise_filter.get_pos_and_avail_premises(
    last_step, last_proof, dset_obj)

available_premises = filtered_result.avail_premises
premise_generator = premise_server.get_ranked_premise_generator(last_step, last_proof, available_premises)

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
    #formatted_lines.append(f"   File: {premises_before[idx].file_path}:{premises_before[idx].line}")
print("Partial Proof:")
print("---------------")
print(last_proof.proof_prefix_to_string(last_step))
print("\nPremise Recommendations:")
print("-----------------------")
print("\n".join(formatted_lines))

    


