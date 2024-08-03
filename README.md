# Rango
Rango is a proof synthesis tool for the Coq theorem prover.
Rango uses _retrieval augmentation_ to adapt to its environment.
This repository contains the code required for:
- Processing data to train Rango, proof retrievers and lemma retrievers
- Training Rango, proof retrievers and lemma retrievers
- Running Rango on proofs in CoqStoq
- Evaluating Rango on CoqStoq's testing set

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
Make sure you have a copy of the CoqHub _data_points_ files in the `raw-data/coq-dataset/data_points` subdirectory of your project.
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
