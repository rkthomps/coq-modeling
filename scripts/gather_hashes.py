import re
import os
import json
import argparse
import subprocess
from pathlib import Path


def fmt_remote(remote: str) -> str:
    remote_match = re.search(r"[:/]([^\/]*\/[^\/]*?)(\.git)?$", remote)
    assert remote_match is not None
    (formatted_remote, _) = remote_match.groups()
    return formatted_remote


def gather_hashes(repos_dir: Path) -> dict[str, str]:
    commits: dict[str, str] = {}
    orig_dir = Path.cwd().resolve()
    for dir in os.listdir(repos_dir):
        os.chdir(repos_dir / dir)
        dir_commit = (
            subprocess.run(["git", "rev-parse", "HEAD"], stdout=subprocess.PIPE)
            .stdout.decode("utf-8")
            .strip()
        )
        dir_url = (
            subprocess.run(
                ["git", "config", "--get", "remote.origin.url"], stdout=subprocess.PIPE
            )
            .stdout.decode("utf-8")
            .strip()
        )
        os.chdir(orig_dir)
        commits[fmt_remote(dir_url)] = dir_commit
    return commits


if __name__ == "__main__":
    parser = argparse.ArgumentParser("Gather commit hashes of all repos.")
    parser.add_argument("repos_dir", help="Directory containing all repos.")
    parser.add_argument("save_loc", help="Location to save the commit hashes.")
    args = parser.parse_args()

    repos_dir = Path(args.repos_dir)
    save_loc = Path(args.save_loc)
    commits = gather_hashes(repos_dir)

    with save_loc.open("w") as f:
        json.dump(commits, f, indent=2)
