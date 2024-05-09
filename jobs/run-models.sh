#!/bin/bash
source venv/bin/activate
python3 src/model_deployment/tactic_gen_server.py fid-local models/t5-fid-small-1024/checkpoint-114500 "expr $SLURM_PROC_ID * 1 + 0"