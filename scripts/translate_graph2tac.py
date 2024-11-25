from __future__ import annotations
import argparse
import os
import json
import ipdb
import re
from enum import Enum
from pathlib import Path
from dataclasses import dataclass
from typing import Optional, Any

from coqstoq.check import Result
from coqstoq.eval_thms import EvalTheorem, get_file_hash, Position
from coqstoq import get_theorem_list, Split

from evaluation.translate import (
    raw_results_to_results,
    RawResult,
    get_save_loc,
    get_coqstoq_split,
    get_thm_hash,
    get_theorem_str,
    get_raw_file_set,
    get_coqstoq_files,
)

import logging


def get_tactician_proof(stdout: str) -> str:
    proof_text = re.sub(r"\u001b\[\d+m", "", stdout)
    proof_text = proof_text.replace("only 1: ", "")
    proof_portion_match = re.search(
        r"synth with cache \((.*?)\)\.\r\nNo more (sub)?goals.", proof_text
    )
    assert proof_portion_match is not None
    (proof_portion, _) = proof_portion_match.groups()
    return proof_portion


def from_json(json_data: Any) -> RawResult:
    print(json_data["file"])
    assert Path(json_data["file"]).is_relative_to("repos")
    project = Path(json_data["file"]).relative_to("repos").parts[0]
    new_path = Path(json_data["file"]).relative_to(Path("repos") / project)
    if json_data["success"]:
        proof = get_tactician_proof(json_data["stdout"])
    else:
        proof = None
    return RawResult(
        project,
        str(new_path),
        json_data["theorem"],
        json_data["success"],
        json_data["synth_time"],
        proof,
    )


def load_tactician_results(path: Path) -> list[RawResult]:
    results: list[RawResult] = []
    for result_file in os.listdir(path):
        with (path / result_file).open() as fin:
            result_data = json.load(fin)
            file_idx_match = re.search(r"(\d+)\.(json|v)$", result_file)
            assert file_idx_match is not None
            (file_idx_str, _) = file_idx_match.groups()
            result = from_json(result_data)
            results.append(result)
    return results


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--tactician_loc", type=str, required=True)
    parser.add_argument("--coqstoq_loc", type=str, required=True)
    parser.add_argument(
        "--split", type=str, required=True, choices=["val", "test", "cutoff"]
    )
    parser.add_argument("--save_loc", type=str, required=True)

    args = parser.parse_args()
    tactician_results = load_tactician_results(Path(args.tactician_loc))
    split = get_coqstoq_split(args.split)
    results = raw_results_to_results(tactician_results, Path(args.coqstoq_loc), split)

    # Save results
    for r in results:
        save_loc = get_save_loc(Path(args.save_loc), r.thm)
        os.makedirs(save_loc.parent, exist_ok=True)
        with save_loc.open("w") as fout:
            json.dump(r.to_json(), fout, indent=2)

    print("Num not none", len(results))
    result_thms = set([get_thm_hash(r.thm) for r in results])
    print("Set size", len(result_thms))

    # find missing
    coqstoq_files = get_coqstoq_files(Path(args.coqstoq_loc), split)
    thms = get_theorem_list(split, Path(args.coqstoq_loc))
    print("Num coqstoq theorems", len(thms))
    proverbot_files = get_raw_file_set(tactician_results)
    because_file_missing = 0
    total = 0
    missing_files: set[Path] = set()
    for t in thms:
        if get_thm_hash(t) not in result_thms:
            thm_path = Path(t.project.workspace.name) / t.path
            if thm_path not in proverbot_files:
                because_file_missing += 1
                missing_files.add(thm_path)
            total += 1
            print("File", thm_path)
            print(get_theorem_str(t, coqstoq_files[thm_path]))
            print()

    print("Because file missing", because_file_missing)
    print("Missing", total)
    for f in sorted(list(missing_files)):
        print(f)
