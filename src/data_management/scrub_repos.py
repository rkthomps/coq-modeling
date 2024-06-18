import sys, os
import re
import argparse
from pathlib import Path

ALLOW_LIST = [
    re.compile(r"_CoqProject"),
    re.compile(r"Makefile"),
    re.compile(r".*?\.v"),
]


def scrub_repos(repos_loc: Path) -> None:
    for root, dirs, files in os.walk(repos_loc):
        for file in files:
            file_path = Path(root) / file
            if not any([pattern.match(file) for pattern in ALLOW_LIST]):
                print(f"Removing {file_path}")
                os.remove(file_path)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        "Scrub repositories to only contain coq files and make files."
    )
    parser.add_argument("repos_loc", type=str, help="Location of repositories.")
    args = parser.parse_args(sys.argv[1:])
    repos_loc = Path(args.repos_loc)
    assert repos_loc.exists()
    proceed = input(f"Scrub {repos_loc}? (y/n): ")
    if proceed.lower() != "y":
        print("Exiting.")
        sys.exit(0)
    scrub_repos(repos_loc)
