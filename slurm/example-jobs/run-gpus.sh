#!/bin/bash
#SBATCH -p gpu-preempt
#SBATCH -t 12:00:00
#SBATCH --nodes=2
#SBATCH --ntasks=16
#SBATCH --gres=gpu:8
#SBATCH --constraint=2080ti#SBATCH --mem=16G
#SBATCH -o slurm-serve-%j.out
srun -l --gres=gpu:1 jobs/run-models.sh
