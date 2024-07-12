#!/bin/bash
#SBATCH -p gpu
#SBATCH --nodes=1
#SBATCH -G 1
#SBATCH --constraint=2080ti
#SBATCH --mem=16G
#SBATCH --time=04:59:00
#SBATCH -o slurm/out/slurm-vector-db-%j.out

MODEL_NAME=select-all-final
CHECKPOINT_NUM=52000
PAGE_SIZE=1024
BATCH_SIZE=64

CHECKPOINT_LOC=models/$MODEL_NAME/checkpoint-$CHECKPOINT_NUM
VECTOR_DB_LOC=data/vector-dbs/$MODEL_NAME

source venv/bin/activate
sbcast raw-data/coq-dataset/sentences.db tmp/sentences.db

LOG_LEVEL=DEBUG python3 src/premise_selection/premise_vector_db.py \
    --db_loc=$VECTOR_DB_LOC \
    --page_size=$PAGE_SIZE \
    --batch_size=$BATCH_SIZE \
    --select_checkpoint=$CHECKPOINT_LOC \
    --sentence_db_loc=raw-data/coq-dataset/sentences.db

