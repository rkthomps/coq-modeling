#!/bin/bash
#SBATCH -p cpu-preempt
#SBATCH -t 00:20:00
#SBATCH -c 1
#SBATCH -o slurm-eval-%j.out

TIMEOUT=00:20:00
TASKS_PER_GPU=1
NUM_GPUS=1
NUM_CPUS=1

source venv/bin/activate
python3 src/evaluation/slurm_eval.py confs/eval.yaml $TIMEOUT $TASKS_PER_GPU $NUM_GPUS $NUM_CPUS
