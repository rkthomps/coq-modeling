
import sys, os
import argparse
import json
from split_raw_data import SPLITS
from shared_thm_graph import FileGraph


def print_safe_files(assignment_loc: str, partition: str, shared_thm_loc: str) -> None:
    with open(assignment_loc, "r") as fin:
        assignment = json.load(fin) 
    candidate_files = assignment[partition] 
    safe_files: list[str] = []
    file_graph = FileGraph.load(shared_thm_loc)

    for candidate_file in candidate_files:
        share_any = False
        for split in SPLITS:
            if split == partition:
                continue 
            for file in assignment[split]:
                if file_graph.share_thm(candidate_file, file):
                    share_any = True
                    break
            if share_any == True:
                break
        if not share_any:
            safe_files.append(candidate_file)

    print(json.dumps(safe_files, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Find safe files (files that dont share thms with a different partition)")
    parser.add_argument("assignment_loc", type=str, help="Location of assignment.")
    parser.add_argument("partition", type=str, help="Partition for which to find safe thms.")
    parser.add_argument("shared_thm_loc", type=str, help="Location of shared theorem file.")
    args = parser.parse_args(sys.argv[1:])
    print_safe_files(args.assignment_loc, args.partition, args.shared_thm_loc)


