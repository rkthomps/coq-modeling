import os
import shutil
import json
import coq_serapy
from dataclasses import dataclass
from pathlib import Path

DATA_PREFIX = Path("../../raw-data/coq-dataset/")
REPO_PREFIX = DATA_PREFIX / "repos"

PROJECTS = [
    "thery-PolTac",
    "coq-contribs-zfc",
    "coq-community-dblib",
]

SAVE_LOC = Path("prefixes")


def collect_project_thms():
    for project in PROJECTS:
        project_num_thms = 0
        project_loc = REPO_PREFIX / project
        assert project_loc.exists()
        for root, _, files in os.walk(project_loc):
            for file in files:
                if file.endswith(".v"):
                    file_loc = Path(root) / file
                    save_file_name = file_loc.relative_to(DATA_PREFIX)
                    file_commands = coq_serapy.load_commands(file_loc)
                    file_thms = coq_serapy.lemmas_in_file(file_loc, file_commands)
                    thm_strs = [thm for _, thm in file_thms]
                    for thm in thm_strs:
                        with file_loc.open("r") as fin:
                            text = fin.read()
                            thm_idx = text.find(thm)
                            prefix = text[:thm_idx]
                            prefix = "Set Tactician Neural Autocache.\n" + prefix
                            prefix = "From Tactician Require Import Ltac1.\n" + prefix
                            prefix += "\n" + thm
                            prefix += "\nsynth.\nQed.\n"
                        save_coq_name = SAVE_LOC / f"{project}-{project_num_thms}.v"
                        save_data_name = SAVE_LOC / f"{project}-{project_num_thms}.json"
                        with save_coq_name.open("w") as fout:
                            fout.write(prefix)
                        with save_data_name.open("w") as fout:
                            thm_data = {
                                "project": project,
                                "file": str(save_file_name),
                                "thm": thm,
                            }
                            fout.write(json.dumps(thm_data, indent=2))
                        project_num_thms += 1


if __name__ == "__main__":
    if SAVE_LOC.exists():
        shutil.rmtree(SAVE_LOC)
    os.makedirs(SAVE_LOC)
    collect_project_thms()
