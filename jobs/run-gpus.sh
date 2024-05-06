#!/bin/bash
#SBATCH -t 2-00
#SBATCH --ntasks=16
#SBATCH --nodes=4
#SBATCH --ntasks-per-node=4
#SBATCH --cpus-per-task=1
#SBATCH --gpus-per-task=1
srun -l jobs/run-models.sh
