#!/bin/bash

REPOS_LOC=raw-data/coq-dataset/repos
TIMEOUT=11:59:59
N_WORKERS=64
N_THREADS_PER_WORKER=4

source venv/bin/activate
LOG_LEVEL=DEBUG python3 src/data_management/compile.py \
    --repos_loc $REPOS_LOC \
    --timeout $TIMEOUT \
    --n_workers $N_WORKERS \
    --n_threads_per_worker $N_THREADS_PER_WORKER