#!/bin/bash
#SBATCH -p gpu-preempt
#SBATCH -t 00:20:00
#SBATCH --ntasks=1
#SBATCH --nodes=1
#SBATCH --gres=gpu:1
#SBATCH --ntasks-per-node=1
#SBATCH --gpus-per-task=1
#SBATCH --cpus-per-task=1
#SBATCH -o slurm-serve-%j.out
#srun -l jobs/run-models.sh
srun -l jobs/sayhi.sh
