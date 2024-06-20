#!/bin/bash
#SBATCH -p cpu-preempt
#SBATCH -c 3
#SBATCH -t 02:00:00
#SBATCH --array=0-3
#SBATCH --mem=16G
#SBATCH -o slurm-out/slurm-prove-%j.out
sbcast sentences.db /tmp/sentences.db
source venv/bin/activate
python3 src/evaluation/eval_worker.py conf.pkl-0619225541 queue-0619225541
