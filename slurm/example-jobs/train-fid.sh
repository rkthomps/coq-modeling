#!/bin/bash
#SBATCH -p gpu-long
#SBATCH --nodes=1
#SBATCH --ntasks-per-node=4      # total number of tasks per node
#SBATCH --gres=gpu:4            # number of gpus per node
#SBATCH --constraint=vram32
#SBATCH --cpus-per-task=4        # cpu-cores per task (>1 if multi-threaded tasks)
#SBATCH --time=01-23:59:00          # total run time limit (HH:MM:SS)
#SBATCH -o slurm-train-fid-%j.out

#SBATCH --mail-type=BEGIN,END,FAIL
#SBATCH --job-name=TRAINFID 	# create a short name for your job
#SBATCH --mem=50GB               # total memory per node



source venv/bin/activate
torchrun --nproc-per-node=4 src/tactic_gen/train_fid.py confs/train_fid.yaml
