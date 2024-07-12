#!/bin/bash
#SBATCH -p gpu-preempt
#SBATCH --nodes=1
#SBATCH --gres=gpu:4            # number of gpus per node
#SBATCH --constraint=vram80
#SBATCH --cpus-per-task=4        # cpu-cores per task (>1 if multi-threaded tasks)
#SBATCH --time=23:59:59
#SBATCH -o slurm/out/slurm-train-select-%j.out

#SBATCH --job-name=TR-SEL 	# create a short name for your job
#SBATCH --no-requeue
#SBATCH --mem=50GB               # total memory per node

source venv/bin/activate
LOG_LEVEL=DEBUG python3 scripts/move_data.py confs/train/select.yaml
torchrun --nproc-per-node=4 --rdzv-backend=c10d --rdzv-endpoint=localhost:0 src/premise_selection/train_select.py confs/train/select.yaml
