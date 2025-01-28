# Rango
Rango is a neural proof synthesis tool for the Coq theorem prover [(see paper)](paper.pdf).
Rango uses _retrieval augmentation_ to adapt to its environment.
This repository contains the code required for:
- Processing data to train Rango, proof retrievers and lemma retrievers
- Training Rango, proof retrievers and lemma retrievers
- Running Rango on proofs in CoqStoq
- Evaluating Rango on CoqStoq's testing set

## CoqStoq Dataset
CoqStoq is a benchmark for evaluating proof sythesis tools for Coq.  
You can access the CoqStoq repository [here](https://github.com/rkthomps/CoqStoq). The CoqStoq repository simply enumerates the theorems in the CoqStoq benchmark and provides an environment for testing proof synthesis tools.

<!-- You can access the CoqStoq dataset [here](https://zenodo.org/records/13188269?token=eyJhbGciOiJIUzUxMiIsImlhdCI6MTcyMjY3MDg5MiwiZXhwIjoxNzM1Njg5NTk5fQ.eyJpZCI6ImRmNmVjMDViLWE1NGUtNDMwOC1hNWEzLTkyOWFlNDRlNWY2ZSIsImRhdGEiOnt9LCJyYW5kb20iOiI1ZDk1Y2U3ZjAzNDJkZjJhYmU3YzBjNTJlMDZhYjc1OCJ9.y7SD3bDwFfPidOQcD-GshfMrEg5yhv0OsxdNC5Up148Xq4_483Yn69Lb3hYhSO3hP_0jkAZ4gJU0ODRIurz2NQ) -->

<!-- ## Trained Models -->
<!-- You can access the language models powering Rango and its variants [here](https://zenodo.org/records/13190944?token=eyJhbGciOiJIUzUxMiIsImlhdCI6MTcyMjY3NzIyOCwiZXhwIjoxNzM1Njg5NTk5fQ.eyJpZCI6ImNjODA2M2MwLTFlNDYtNDljZS05ZjkzLTAxYWNiYjhhMGY0ZSIsImRhdGEiOnt9LCJyYW5kb20iOiJjNDA2ZmVjNzhmMWRkNzAzNzVmNDRjOWJhMTIxNzY4OSJ9.AY9p1oeV_I4L44MQRDHTgpQU9xlDKbK805zLo22wZ9GZZQTKvfbB8mWxFuqjHSMLswLeT_5CuvS_M9vZa12lMw) -->

## Artifact
The easiest way to replicate our project is using the replication package provided here [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.14757301.svg)](https://doi.org/10.5281/zenodo.14757301).
Once you download the replication package, you should follow [ARTIFACT.md](ARTIFACT.md) to build a docker image, and run replication commands in a docker container.

## Source Code Documentation
You can find a high-level overview of the source code in [MAP.md](MAP.md).

## Local Setup
The following instructions apply if you want to set up this repository without docker. Note that we ran most of our experiments using SLURM on a cluster. If you do not have slurm, or you do not have access to GPUs, you will only be able to run a subset of the following commands.  

  ### Setup
  - **Install Dependencies:**
      1. Install repo:
        ```
        git clone --recurse-submodules https://github.com/rkthomps/coq-modeling
        pip3 install -e .
        cd coqpyt
        pip3 install .
        cd ../CoqStoq
        pip3 install -e .
        ```
    
      2. Install opam and build CoqStoq Projects: Refer to the [CoqStoq README](https://github.com/rkthomps/CoqStoq/blob/main/README.md)
          

  ### Running Rango on a CoqStoq Project
  1. Ensure you have the Rango model downloaded (TODO: Put Rango model on huggingface.) 
  2. Ensure you have CoqStoq properly built `cd CoqStoq` then `pytest` 
  3. Ensure the CoqStoq data is arranged as follows:
    - Rango assumes that data has the following directory structure during evaluation:
    ```
      <name-of-dataset>
        /data_points
        /repos
        <name-of-dataset>-sentences.db
    ```
    - The `data_points` folder contains DatasetFile objects that let Rango know what premises and proofs are available in the context when synthesizing a proof. There is one file in this folder for every `.v` file in the repos folder.  
    - The `repos` folder contains all of the repositories that have the theorems on which Rango will be evaluated. 

    **Example**  
    Suppose I wanted to create a dataset called "coqstoq-test" for example comprised of the theorems from the testing split of CoqStoq. I would do the following:  
    1. `mkdir coqstoq-test` 
    2. `ln -s CoqStoq/test-repos coqstoq-test/repos`
    3. ``` 
        rm -rf ~/.cache/coqpyt_cache
        python3 scripts/create_coqstoq_data_points CoqStoq test coqstoq-test/data_points coqstoq-test/coqstoq-test-sentences.db
        ```
        - "CoqStoq" is the path to the CoqStoq repository
        - "test" is the split of CoqStoq for which we want to create data 
        - "coqstoq-test/data_points" is where we want to save the data points 
        - "coqstoq-test-sentences.db" is where we want to save the sentencedb (Contains shared premises between files.)


  ### Running the Evaluation
  You can run Rango on a dataset like the one above with either of the following scripts: 
  ```
  python3 src/evaluation/eval.py \
  --conf_loc=example_confs/eval/coqstoq-test.yaml \
  --slurm_conf=example_confs/slurm/gpu8.yaml

  python3 src/evaluation/eval.py \
  --conf_loc=example_confs/eval/coqstoq-test.yaml \
  --n_workers=1
  ```
  The prior requires access to a slurm cluster.
  The latter will run the evaluation with one worker.  
  Note that the configuration for the evaluation is in the file `example_confs/eval/coqstoq-test.yaml`. Depending on what you are evaluating, it is likely you will have to change paths in this configuration file. 

  ### Processing Data
  Make sure you have a copy of the CoqStoq _data_points_ files in the `raw-data/coq-dataset/data_points` subdirectory of your project.
  Then, with access to a slurm cluster, you may preprocess your dataset by running the command:
  `bash slurm/example-jobs/create_dataset.sh`. This command creates a dataset following a configuration file specified by a constant in the script. 
  Example configuration files can be found in `example-confs/data/lm.yaml`, `example-confs/data/premise.yaml`, and `example-confs/data/rerank.yaml` for tactic generation, dense retrieval, and reranking respectively.

  Before using your processed data to train models you must "consolidate it" into sqlite databases. 
  You can consolidate a dataset as follows: `python3 src/data_management/consolidate.py <split location> <dataset location> <new dataset location>`
  Split location is likely `splits/final-split.json`, but you can also use an inter-file split: `splits/random-split.json`. 
  Consolidating will create a directory with a `train.db` `val.db` and `test.db` file with training, validation and testing examples.

  ### Doing Training
  You can train a model by running
  `sbatch slurm/example-jobs/train_decoder.sh`
  This commmand will use the configuration file stored in `confs/train/decoder.yaml`. Example configuration files for training can be found in `example-confs/train/decoder.yaml`
  You can also train dense retrival models and rerankers with the `train_select.sh` and `train_rerank.sh` scripts in the `slurm/example-jobs` directory.



