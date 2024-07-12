#!/bin/bash

CONF=confs/eval/premise.yaml
TIMEOUT=04:59:59
N_GPU_NODES=2
N_DEVICES_PER_NODE=8
N_WORKERS=16 # Will be ignored if gpus are present
N_THREADS_PER_WORKER=3

LOG_LEVEL=DEBUG python3 src/evaluation/premise_eval.py \
    --conf_loc=$CONF \
    --timeout=$TIMEOUT \
    --n_gpu_nodes=$N_GPU_NODES \
    --n_devices_per_node=$N_DEVICES_PER_NODE \
    --n_workers=$N_WORKERS \
    --n_threads_per_worker=$N_THREADS_PER_WORKER