from pathlib import Path
from data_management.splits import DataSplit, Split
from data_management.sentence_db import SentenceDB

DATA_SPLIT_LOC = Path("splits/final-split.json")
DATA_LOC = Path("raw-data/coq-dataset")
SENTENCE_DB_LOC = Path("raw-data/coq-dataset/sentences.db")

data_split = DataSplit.load(DATA_SPLIT_LOC)
sentence_db = SentenceDB.load(SENTENCE_DB_LOC)

exclude = set(
    [
        "coq-contribs-chinese-Zbase.v",
        "coq-contribs-dep-map-Coqlib.v",
        "CertiKOS-coqrel-RelDefinitions.v",
        "CertiKOS-coqrel-OptionRel.v",
        "CertiKOS-coqrel-RDestruct.v",
        "coq-contribs-chinese-Lci.v",
        "CertiKOS-coqrel-Relators.v",
        "CertiKOS-coqrel-KLR.v",
        "coq-contribs-fermat4-Descent.v",
        "coq-contribs-chinese-Nat_complements.v",
        "coq-contribs-weak-up-to-Relations.v",
        "coq-community-coqoban-theories-Coqoban_engine.v",
        "CertiKOS-coqrel-Monotonicity.v",
        "CertiKOS-coqrel-MorphismsInterop.v",
        "coq-contribs-zchinese-Lci.v",
        "CertiKOS-coqrel-RelClasses.v",
    ]
)

num_ind_proofs = 0
proof_ind_dict: dict[str, int] = {}

num_proofs = 0
proof_dict: dict[str, int] = {}
for file in data_split.get_file_list(Split.TEST):
    dp_file = file.get_dp(DATA_LOC, sentence_db)
    if dp_file.dp_name in exclude:
        print("in exclude")
        continue
    if file.repository not in proof_ind_dict:
        proof_ind_dict[file.repository] = 0
    if file.repository not in proof_dict:
        proof_dict[file.repository] = 0
    file_num_ind_proofs = len([p for p in dp_file.proofs if p.is_proof_independent()])
    file_num_proofs = len(dp_file.proofs)

    proof_dict[file.repository] += file_num_proofs
    proof_ind_dict[file.repository] += file_num_ind_proofs
    num_proofs += file_num_proofs
    num_ind_proofs += file_num_ind_proofs
    print(f"Num Proofs: {num_proofs}; Num Ind Proofs: {num_ind_proofs}\r", end="")

print(proof_dict)
print("Final num proofs: ", num_proofs)

print()
print(proof_ind_dict)
print("Final num ind proofs: ", num_ind_proofs)
