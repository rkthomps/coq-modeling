

import requests
import json

from tactic_gen.lm_example import BasicLmExample
from premise_selection.premise_formatter import (
    PremiseFormat, PREMISE_ALIASES, ContextFormat, CONTEXT_ALIASES)
from model_deployment.serve_prem_utils import (
    FormatResponse, PremiseRequest, PremiseResponse, FORMAT_ENDPOINT, PREMISE_ENDPOINT)
from model_deployment.serve_prem_utils import FormatResponse, PremiseRequest, PremiseResponse
from model_deployment.searcher import ProofManager

URL = "http://127.0.0.1:5000"
#FILE = "/home/ubuntu/coq-modeling/test-coq-projs/min_superlist.v"
#FILE = "/home/ubuntu/coq-modeling/test-coq-projs/min.v"
FILE = "/home/ubuntu/coq-modeling/test-coq-projs/harder_example.v"
N = 20

format_endpoint = URL + FORMAT_ENDPOINT
premise_endpoint = URL + PREMISE_ENDPOINT 

# format_response = requests.post(format_endpoint, {})
# format_response_dict = json.loads(format_response.content)
# format_obj = FormatResponse.from_json(format_response_dict)

# context_format = CONTEXT_ALIASES[format_obj.context_format_alias]
# premise_format = PREMISE_ALIASES[format_obj.preise_format_alias]

# TODO: ACCESS context through proof manager to get premise selection ex.
with ProofManager(FILE, BasicLmExample) as pm:
    dset_obj = pm.get_dataset_file("")
    last_proof = dset_obj.proofs[-1]
    last_step = last_proof.steps[-1]
    exit()

context_str = context_format.format(last_step, last_proof)
premises_before = dset_obj.get_premises_before(last_proof)
premise_strs: list[str] = []
for premise in premises_before:
    formatted_premise = premise_format.format(premise)
    premise_strs.append(formatted_premise)

premise_request = PremiseRequest(context_str, premise_strs)
response_data = requests.post(premise_endpoint, premise_request.to_request_data())
premise_response = PremiseResponse.from_json(json.loads(response_data.content))

num_premises = len(premise_response.premise_scores)
assert num_premises == len(premises_before)
arg_sorted_prems = sorted(range(num_premises), 
                          key=lambda idx: -1 * premise_response.premise_scores[idx])

formatted_lines: list[str] = []
for i, idx in enumerate(arg_sorted_prems[:20]):
    prefix = "Rec. {:3d}: ".format(i)
    lines = premises_before[idx].text.split("\n")
    for line in lines:
        formatted_line = prefix + line
        formatted_lines.append(formatted_line)
        prefix = " " * len(prefix)
    #formatted_lines.append(f"   File: {premises_before[idx].file_path}:{premises_before[idx].line}")
print("Partial Proof:")
print("---------------")
print(last_proof.proof_prefix_to_string(last_step))
print("\nPremise Recommendations:")
print("-----------------------")
print("\n".join(formatted_lines))

    


