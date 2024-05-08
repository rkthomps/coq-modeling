#!/bin/bash
python3 src/model_deployment/tactic_gen_server.py models/t5-fid-small-whole-proof-ret/checkpoint-110500 "expr $SLURM_PROC_ID * 1 + 0"