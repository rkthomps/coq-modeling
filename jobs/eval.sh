#!/bin/bash

TIMEOUT=02:00:00
NUM_GPUS=2
NUM_WORKERS=4
NUM_THREADS_PER_WORKER=3

source venv/bin/activate
LOG_LEVEL=DEBUG python3 src/evaluation/slurm_eval.py confs/eval.yaml $TIMEOUT $NUM_GPUS $NUM_WORKERS $NUM_THREADS_PER_WORKER 
