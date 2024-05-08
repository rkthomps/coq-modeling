#!/bin/bash
#SBATCH -p cpu-preempt
#SBATCH -t 00:20:00
#SBATCH -c 1

TIMEOUT=00:20:00
TASKS_PER_GPU=1
NUM_GPUS=1
NUM_CPUS=1

python3 src/evaluation/slurm_eval.py conf/eval.yaml $TIMEOUT $TASKS_PER_GPU $NUM_GPUS $NUM_CPUS
