import os
import re
import json
from pathlib import Path
from typing import Optional
from data_management.create_file_data_point import (
    get_data_point,
    get_switch_loc,
    NoProofsError,
)
from data_management.splits import DataSplit, file_from_split, Split
from data_management.sentence_db import SentenceDB
from coqpyt.coq.base_file import CoqFile
from coqpyt.coq.proof_file import ProofFile

from model_deployment.fast_client import FastLspClient, ClientWrapper

from util.util import set_rango_logger
import logging

FILE_LOC = str(
    Path("raw-data/coq-dataset/repos/AbsInt-CompCert/arm/SelectLongproof.v").resolve()
)
WORKSPACE_LOC = str(Path("raw-data/coq-dataset/AbsInt-CompCert").resolve())


def run_coq_file():
    with CoqFile(FILE_LOC, workspace=WORKSPACE_LOC) as coq_file:
        coq_file.run()
        assert coq_file.is_valid


def run_coq_lsp():
    root_uri = f"file://{WORKSPACE_LOC}"
    file_uri = f"file://{FILE_LOC}"
    client = FastLspClient(root_uri)
    try:
        wrapper = ClientWrapper(client, file_uri)
        with open(FILE_LOC, "r") as f:
            text = f.read()
        wrapper.write_and_get_steps(text)

        valid = True
        for diagnostic in client.lsp_endpoint.diagnostics[wrapper.file_uri]:
            if diagnostic.severity == 1:
                valid = False
        assert valid
    finally:
        client.kill()


def run_proof_file():
    with ProofFile(
        FILE_LOC, workspace=WORKSPACE_LOC, use_disk_cache=True
    ) as proof_file:
        proof_file.run()
    print("Num proofs", len(proof_file.proofs))


def run_data_point():
    sentence_db = SentenceDB.load(Path("raw-data/coq-dataset/sentences.db"))
    switch_loc = get_switch_loc()
    get_data_point(
        Path(FILE_LOC),
        Path(WORKSPACE_LOC),
        sentence_db,
        add_to_dataset=True,
        switch_loc=switch_loc,
    )


if __name__ == "__main__":
    run_coq_lsp()
    # run_coq_file()
    # run_proof_file()
    # run_data_point()
