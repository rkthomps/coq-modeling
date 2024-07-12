#!/bin/bash
#SBATCH -p gpu-preempt
#SBATCH -t 23:59:59
#SBATCH --nodes=1
#SBATCH -c 8
#SBATCH -G 8
#SBATCH --constraint=2080ti
#SBATCH --mem=64G
#SBATCH -o slurm/out/slurm-proof-db-%j.out
#SBATCH --no-requeue

cp -r raw-data/coq-dataset/sentences.db /tmp/sentences.db
cp -r raw-data/coq-dataset/data_points /tmp/data_points
source venv/bin/activate
LOG_LEVEL=DEBUG python3 src/proof_retrieval/proof_vector_db.py confs/data/proof-vector-db.yaml