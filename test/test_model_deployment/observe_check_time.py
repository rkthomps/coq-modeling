from pathlib import Path
import time

from util.test_utils import MINI_TEST_PROJET_LOC
from model_deployment.fast_client import ClientWrapper, FastLspClient
from coqpyt.lsp.structs import *
from coqpyt.coq.lsp.structs import *
from coqpyt.coq.structs import *

MY_FILE = MINI_TEST_PROJET_LOC / "theories" / "Induction.v"


def read_my_file():
    with MY_FILE.open("r") as fin:
        return fin.read()


def get_empty_contents():
    return ""


def time_write(idx: int, c: ClientWrapper, contents: str) -> list[Step]:
    start = time.time()
    steps = c.write_and_get_steps(contents)
    end = time.time()
    print(f"{idx}th time:", end - start)
    return steps


def time_goals(idx: int, c: ClientWrapper, p: Position):
    start = time.time()
    c.client.proof_goals(TextDocumentIdentifier(c.file_uri), p)
    end = time.time()
    print(f"{idx}th goal time: ", end - start)


def run_time_check():
    workspace_uri = f"file://{MINI_TEST_PROJET_LOC.resolve()}"
    my_client = FastLspClient(workspace_uri)
    try:
        file_uri = f"file://{MY_FILE}"
        client_wrapper = ClientWrapper(my_client, file_uri)
        file_contents = read_my_file()
        steps0 = time_write(0, client_wrapper, file_contents)
        time_goals(0, client_wrapper, steps0[-1].ast.range.end)
        time_write(1, client_wrapper, file_contents)
        file_contents_2 = file_contents + "\n" + file_contents
        time_write(2, client_wrapper, file_contents_2)
        time_write(3, client_wrapper, file_contents)
        time_goals(3, client_wrapper, steps0[-1].ast.range.end)

    finally:
        my_client.kill()


if __name__ == "__main__":
    run_time_check()
