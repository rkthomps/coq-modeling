#!/bin/bash
#CONF=confs/data/lm.yaml
#CONF=confs/data/premise.yaml
CONF=confs/data/rerank.yaml
TIMEOUT=23:59:59
N_GPU_NODES=0
N_DEVICES_PER_NODE=8
#N_WORKERS=256
N_WORKERS=64
N_THREADS_PER_WORKER=4

source venv/bin/activate
LOG_LEVEL=DEBUG python3 src/data_management/create_dataset.py \
    $CONF \
    $TIMEOUT \
    $N_GPU_NODES \
    $N_DEVICES_PER_NODE \
    $N_WORKERS \
    $N_THREADS_PER_WORKER 

