#!/bin/bash
#SBATCH -p gpu-preempt
#SBATCH --nodes=1
#SBATCH --ntasks-per-node=4      # total number of tasks per node
#SBATCH --gres=gpu:4            # number of gpus per node
#SBATCH --constraint=vram80
#SBATCH --cpus-per-task=4        # cpu-cores per task (>1 if multi-threaded tasks)
#SBATCH --time=01-23:59:00          # total run time limit (HH:MM:SS)
#SBATCH -o slurm-train-fid-%j.out

#SBATCH --mail-type=BEGIN,END,FAIL
#SBATCH --job-name=TRAINFID 	# create a short name for your job
#SBATCH --mem=50GB               # total memory per node


source venv/bin/activate
python3 scripts/move_data.py confs/train_decoder.yaml
torchrun --nproc-per-node=4 src/tactic_gen/train_decoder.py confs/train_decoder.yaml
