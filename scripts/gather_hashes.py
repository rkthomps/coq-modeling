import re
import os
import json
import argparse
import subprocess
from pathlib import Path

import logging

from util.constants import RANGO_LOGGER
from util.util import set_rango_logger

_logger = logging.getLogger(RANGO_LOGGER)


def fmt_remote(remote: str) -> str:
    remote_match = re.search(r"[:/]([^\/]*\/[^\/]*?)(\.git)?$", remote)
    assert remote_match is not None
    (formatted_remote, _) = remote_match.groups()
    return formatted_remote


def gather_hashes(repos_dir: Path) -> dict[str, str]:
    commits: dict[str, str] = {}
    orig_dir = Path.cwd().resolve()
    for i, dir in enumerate(os.listdir(repos_dir)):
        try:
            os.chdir(repos_dir / dir)
            dir_commit = (
                subprocess.run(["git", "rev-parse", "HEAD"], stdout=subprocess.PIPE)
                .stdout.decode("utf-8")
                .strip()
            )
            dir_url = (
                subprocess.run(
                    ["git", "config", "--get", "remote.origin.url"],
                    stdout=subprocess.PIPE,
                )
                .stdout.decode("utf-8")
                .strip()
            )
            commits[fmt_remote(dir_url)] = dir_commit
            if 0 < i and i % 100 == 0:
                _logger.info(f"Processed {i} repos.")
        except PermissionError:
            _logger.error(f"Permission error for {dir}.")
            continue
        finally:
            os.chdir(orig_dir)
    return commits


if __name__ == "__main__":
    parser = argparse.ArgumentParser("Gather commit hashes of all repos.")
    parser.add_argument("repos_dir", help="Directory containing all repos.")
    parser.add_argument("save_loc", help="Location to save the commit hashes.")
    args = parser.parse_args()
    set_rango_logger(__file__, logging.DEBUG)

    repos_dir = Path(args.repos_dir)
    save_loc = Path(args.save_loc)
    commits = gather_hashes(repos_dir)

    with save_loc.open("w") as f:
        json.dump(commits, f, indent=2)
