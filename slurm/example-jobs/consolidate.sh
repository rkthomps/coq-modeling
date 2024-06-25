#!/bin/bash
#SBATCH -p cpu-preempt
#SBATCH -c 4
#SBATCH -t 11:59:59
#SBATCH --mem=64G
#SBATCH -o slurm/out/slurm-consolidate-%j.out
#SBATCH --job-name=consolidate
IN_DATA_LOC=data/general-random-nstep
OUT_DATA_LOC=data/general-random-nstep-clean
source venv/bin/activate
LOG_LEVEL=DEBUG python3 src/data_management/consolidate.py  $IN_DATA_LOC $OUT_DATA_LOC
