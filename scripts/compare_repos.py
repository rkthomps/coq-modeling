from typing import Optional

import json
import os
import re
import argparse
from pathlib import Path
import subprocess
from dataclasses import dataclass


parser = argparse.ArgumentParser("Compare repo 1 to repo 2.")

names = [
    ("coq-community-qarith-stern-brocot", "coq-community/qarith-stern-brocot"),
    ("coq-community-bertrand", "coq-community/bertrand"),
    ("coq-community-dblib", "coq-community/dblib"),
    ("coq-contribs-zfc", "coq-contribs/zfc"),
    ("coq-community-zorns-lemma", "coq-community/zorns-lemma"),
    ("coq-community-coq-ext-lib", "coq-community/coq-ext-lib"),
    ("coq-community-hoare-tut", "coq-community/hoare-tut"),
    ("coq-community-coqeal", "coq-community/coqeal"),
    ("coq-community-math-classes", "coq-community/math-classes"),
    ("coq-community-huffman", "coq-community/huffman"),
    ("thery-PolTac", "thery/PolTac"),
    ("coq-community-buchberger", "coq-community/buchberger"),
    ("coq-community-stalmarck", "coq-community/stalmarck"),
    ("coq-community-fourcolor", "coq-community/fourcolor"),
    ("coq-community-sudoku", "coq-community/sudoku"),
    ("coq-community-graph-theory", "coq-community/graph-theory"),
    ("coq-community-reglang", "coq-community/reglang"),
    ("AbsInt-CompCert", "AbsInt/CompCert"),
]

OLD_REPO_LOC = Path("raw-data/coq-dataset/repos").resolve()
NEW_REPO_LOC = Path("raw-data/coq-dataset/repos-cmp").resolve()


def check_contents(old_repo_loc: Path, new_repo_loc: Path) -> bool:
    for root, _, files in os.walk(new_repo_loc):
        if ".git" in root:
            continue
        for file in files:
            old_file_loc = old_repo_loc / Path(root).relative_to(new_repo_loc) / file
            new_file_loc = Path(root) / file
            if not old_file_loc.exists():
                print(f"File {old_file_loc} does not exist.")
                return False
            with open(old_file_loc, "rb") as old_file, open(
                new_file_loc, "rb"
            ) as new_file:
                old_contents = old_file.read()
                new_contents = new_file.read()
                if not old_contents == new_contents:
                    print(f"For file {old_file_loc}, contents do not match.")
                    return False
    return True


def get_next_commit() -> str:
    log_out = subprocess.run(
        ["git", "log", "-n", "2", "--oneline"], stdout=subprocess.PIPE
    )
    log = log_out.stdout.decode("utf-8").strip().split("\n")
    assert len(log) == 2
    return log[1].split(" ")[0]


@dataclass
class FoundCommit:
    commit: str
    date: str
    step: int


def get_matching_commit(old_name: str, new_name: str) -> Optional[FoundCommit]:
    orig_dir = Path.cwd().resolve()
    old_loc = (OLD_REPO_LOC / old_name).resolve()
    new_loc = (NEW_REPO_LOC / new_name.split("/")[1]).resolve()

    os.chdir(NEW_REPO_LOC)
    try:
        # print(new_loc)
        if not new_loc.exists():
            subprocess.run(["git", "clone", f"git@github.com:{new_name}.git"])

        assert new_loc.exists()
        os.chdir(new_loc)
        subprocess.run(["git", "checkout", "master"])
        subprocess.run(["git", "checkout", "main"])

        num_steps = 0
        while not check_contents(old_loc, new_loc):
            print(f"Check {num_steps} failed.")
            num_steps += 1
            next_commit = get_next_commit()
            # print(f"Checking out {next_commit}.")
            subprocess.run(["git", "checkout", next_commit])
            if num_steps > 100:
                print(f"Failed to converge for {new_name}.")
                return None

        final_commit = subprocess.run(
            ["git", "rev-parse", "HEAD"], stdout=subprocess.PIPE
        )
        commit_date = subprocess.run(
            ["git", "show", "-s", "--format=%ci", "HEAD"], stdout=subprocess.PIPE
        )
        return FoundCommit(
            commit=final_commit.stdout.decode("utf-8").strip(),
            date=commit_date.stdout.decode("utf-8").strip(),
            step=num_steps,
        )
    finally:
        os.chdir(orig_dir)


matching_commits: dict[str, Optional[FoundCommit]] = {}
for o, n in names:
    matching_commits[n] = get_matching_commit(o, n)

for n, c in matching_commits.items():
    if c is not None:
        print(f"{n}: {c.commit} ({c.date}) in {c.step} steps.")
    else:
        print(f"{n}: None")

test_commits: dict[str, str] = {}
for m, v in matching_commits.items():
    if v is not None:
        test_commits[m] = v.commit

print(Path.cwd())
with open("commits.json", "w") as fout:
    json.dump(test_commits, fout, indent=2)

# qarith: c8639f188ab2e1ea3904cd27f5b720e8502e92a9
# bertrand:
# dblib:
# zfc:
# zorns-lemma:
# coq-ext-lib:
# hoare-tut:
# coqeal:
# math-classes:
# huffman:
# PolTac:
# buchberger:
# stalmarck:
# fourcolor:
# sudoku:
# graph-theory:
# reglang:
# AbsInt-CompCert
