from pathlib import Path
from data_management.splits import DataSplit
import re

from coqstoq import get_theorem_list, Split


SPLIT_LOC = Path("splits/icse-off-rnd-intersect.json")
COQSTOQ_LOC = Path("/work/pi_brun_umass_edu/kthompson/CoqStoq")

split = DataSplit.load(SPLIT_LOC)

project_name_map: dict[str, str] = {
    ".": "compcert",
    "AbsInt-CompCert": "compcert",
    "coq-community-buchberger": "buchberger",
    "coq-community-coq-ext-lib": "ext-lib",
    "coq-community-dblib": "dblib",
    "coq-community-fourcolor": "fourcolor",
    "coq-community-hoare-tut": "hoare-tut",
    "coq-community-huffman": "huffman",
    "coq-community-math-classes": "math-classes",
    "coq-community-reglang": "reglang",
    "coq-community-zorns-lemma": "zorns-lemma",
    "coq-contribs-zfc": "zfc",
    "thery-PolTac": "poltac",
}


print(len(split.test_files))
available_test_files: set[Path] = set()
for f in split.test_files:
    assert Path(f.file).is_relative_to(Path("repos"))
    coqstoq_file_name = Path(f.file).relative_to(Path("repos"))
    first_part = coqstoq_file_name.parts[0]
    if first_part not in project_name_map:
        print(f"Skipping {first_part}. Not found.")
        continue
    new_first_part = project_name_map[first_part]
    coqstoq_path = Path(new_first_part, *coqstoq_file_name.parts[1:])
    available_test_files.add(coqstoq_path)


coqstoq_indices: list[int] = []
coqstoq_thms = get_theorem_list(Split.TEST, COQSTOQ_LOC)
for i, thm in enumerate(coqstoq_thms):
    thm_path = thm.project.workspace.name / thm.path
    if thm_path in available_test_files:
        coqstoq_indices.append(i)

print(len(coqstoq_indices))

for ci in coqstoq_indices:
    thm = coqstoq_thms[ci]
    thm_path = thm.project.workspace.name / thm.path
    assert thm_path in available_test_files

print(coqstoq_indices[:500])
