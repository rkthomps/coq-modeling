#!./venv/bin/python3
import sys, os
import argparse
import requests
from pathlib import Path
from util.socket_client import ServerAdapter


def ping(socket: Path):
    session = requests.Session()
    url = f"http://test/"
    session.mount(url, ServerAdapter(socket))
    response = session.get(url)
    print(response)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("socket")

    args = parser.parse_args(sys.argv[1:])
    socket = Path(args.socket)
    ping(socket)
