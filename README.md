# Rango
Rango is a proof synthesis tool for the Coq theorem prover.
Rango uses _retrieval augmentation_ to adapt to its environment.
This repository contains the code required for:
- Processing data to train Rango, proof retrievers and lemma retrievers
- Training Rango, proof retrievers and lemma retrievers
- Running Rango on proofs in CoqStoq
- Evaluating Rango on CoqStoq's testing set

## CoqStoq Dataset
You can access the CoqStoq dataset [here](https://zenodo.org/records/13188269?token=eyJhbGciOiJIUzUxMiIsImlhdCI6MTcyMjY3MDg5MiwiZXhwIjoxNzM1Njg5NTk5fQ.eyJpZCI6ImRmNmVjMDViLWE1NGUtNDMwOC1hNWEzLTkyOWFlNDRlNWY2ZSIsImRhdGEiOnt9LCJyYW5kb20iOiI1ZDk1Y2U3ZjAzNDJkZjJhYmU3YzBjNTJlMDZhYjc1OCJ9.y7SD3bDwFfPidOQcD-GshfMrEg5yhv0OsxdNC5Up148Xq4_483Yn69Lb3hYhSO3hP_0jkAZ4gJU0ODRIurz2NQ)

## Trained Models
You can the language models powering Rango and its variants [here](https://zenodo.org/records/13190944?token=eyJhbGciOiJIUzUxMiIsImlhdCI6MTcyMjY3NzIyOCwiZXhwIjoxNzM1Njg5NTk5fQ.eyJpZCI6ImNjODA2M2MwLTFlNDYtNDljZS05ZjkzLTAxYWNiYjhhMGY0ZSIsImRhdGEiOnt9LCJyYW5kb20iOiJjNDA2ZmVjNzhmMWRkNzAzNzVmNDRjOWJhMTIxNzY4OSJ9.AY9p1oeV_I4L44MQRDHTgpQU9xlDKbK805zLo22wZ9GZZQTKvfbB8mWxFuqjHSMLswLeT_5CuvS_M9vZa12lMw)

## Setup
- **Install Dependencies:**
    - Install repo:
      - `git clone --recurse-submodules https://github.com/rkthomps/coq-modeling`
      - `pip3 install -e .`
      - `cd coqpyt`
      - `pip3 install .`
        
    - Install opam (Ocaml package manager):
      - `sudo apt-get update && sudo apt-get install opam`.
      - `opam init`
      - `eval $(opam env --switch=default)`
     
    - Install Coq:
      - `opam pin add coq 8.18.0`
        
    - Install coq-lsp:
      - `opam install coq-lsp`


## Processing Data
Make sure you have a copy of the CoqStoq _data_points_ files in the `raw-data/coq-dataset/data_points` subdirectory of your project.
Then, with access to a slurm cluster, you may preprocess your dataset by running the command:
`bash slurm/example-jobs/create_dataset.sh`. This command creates a dataset following a configuration file specified by a constant in the script. 
Example configuration files can be found in `example-confs/data/lm.yaml`, `example-confs/data/premise.yaml`, and `example-confs/data/rerank.yaml` for tactic generation, dense retrieval, and reranking respectively.

Before using your processed data to train models you must "consolidate it" into sqlite databases. 
You can consolidate a dataset as follows: `python3 src/data_management/consolidate.py <split location> <dataset location> <new dataset location>`
Split location is likely `splits/final-split.json`, but you can also use an inter-file split: `splits/random-split.json`. 
Consolidating will create a directory with a `train.db` `val.db` and `test.db` file with training, validation and testing examples.

## Training Models
You can train a model by running
`sbatch slurm/example-jobs/train_decoder.sh`
This commmand will use the configuration file stored in `confs/train/decoder.yaml`. Example configuration files for training can be found in `example-confs/train/decoder.yaml`
You can also train dense retrival models and rerankers with the `train_select.sh` and `train_rerank.sh` scripts in the `slurm/example-jobs` directory.

## Evaluating Models
With access to a slurm cluster, you can evaluate a trained model using the command `bash slurm/jobs/eval.sh`.
This evaluation uses a configuration file. There is an example configuration file in `example-confs/eval/proofs.yaml`

## Inspecting Results
You can inspect the results of the evaluated models using the notebook `notebooks/evaluation/eval.ipynb`

## Running Single Proofs
You can run Rango on a single coq proof from the CoqHub dataset with `python3 scripts/run.py prove confs/single.yaml 0`. 
Make sure you have access to a gpu when you run this command. 
