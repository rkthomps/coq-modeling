#!/bin/bash
source venv/bin/activate
python3 src/model_deployment/tactic_gen_server.py decoder-local models/deepseek-proof-prem-final/checkpoint-52000 $(expr $SLURM_PROCID \* 1 + 0)