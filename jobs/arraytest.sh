#!/bin/bash

#SBATCH --array=0-7
#SBATCH -G 8
#SBATCH -p gpu-preempt
#SBATCH -t 00:01:00

echo $SLURM_ARRAY_TASK_ID
echo $CUDA_VISIBLE_DEVICES
echo $GPU_DEVICE_ORDINAL
