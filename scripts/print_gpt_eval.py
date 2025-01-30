import json
from pathlib import Path
from model_deployment.whole_proof_searcher import WholeProofSuccess, WholeProofFailure

LOC = Path(
    "/home/ubuntu/coq-modeling/evaluations/coqstoq-results/cutoff-gpt-4o/pnvrocqlib/theories/Math/ClassicalDomainTheory.v/424-0.json"
)

with open(LOC) as f:
    f_data = json.load(f)
    for attempt in f_data["attempted_proofs"]:
        print(attempt)
