#!/bin/bash
#SBATCH -c 16
#SBATCH -t 2-00
#SBATCH --array=0-5732%16
timout 240 python3 src/evaluation/eval_proof.py proof_maps/val $SLURM_ARRAY_TASK_ID
