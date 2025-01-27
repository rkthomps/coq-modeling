# Artifact for "Rango: Adaptive Retrieval-Augmented Proving for Automated Software Verification"


## Purpose
This artifact is applying for the following badges:
- Available
- Functional
- Reusable

This artifact deserves each of the listed badges for the following reasons.

### Available
All models, data and code are publically available and stored in an archival source [#INSERT LINK]

### Functional
- The artifact can replicate all of the main results (tables 1 through 10) from the [# link this paper] using cached results. 
- The artifact contains a script that allows users to run any model appearing in the [# link this paper] on any theorem in our benchmark -- enabling complete replication of results given enough time. 

### Reusable
System is well-documented with a map of the source code [#DO SOURCE CODE MAP]

## Provenance
[# INSERT LINK]

## Data
The artifcat contains the entire corpus of data used to train and evaluate Rango.  
The data resides in the raw-data folder of the artifact and is split into four locations: 
- coq-dataset
- coqstoq-test
- coqstoq-val
- coqstoq-cutoff

To use this data, one must load the json objects  in these folders into `DatasetFile` objects defined in `src/data_management/dataset_file.py`.
An example on how to do this (and an example which tabulates aggregate statistics about the dataset) is given in the section of `scripts/replicate.py` that replicates table 1. 


## Setup
The replication package is a docker image that interfaces with local GPUs using the [`nvidia-container-toolkit`](https://docs.nvidia.com/datacenter/cloud-native/container-toolkit/latest/install-guide.html#installing-with-apt).
To build this artifact, you must: 
- Have a machine that has at least one NVIDA GPU with at least 11GB of VRAM. 
- Have docker installed on the machine. 
- Have at least 50GB of disk space available for the docker image and container. 
- Have `nvidia-container-toolkit` installed on the machine.

1. Download the replication package.
2. Build the replication package:
   ```
   docker build --build-arg CUDA_VERSION=12.4.1 -t rango .
   ```
   Note that the image has been tested using CUDA 12.4.1. 
   Depending on the driver for your GPUs, you may need to build the image 
   with a different cuda version. 
   You can check the latest cuda version supported by your drivers using `nvidia-smi`. 
   You can check the exact cuda version of your drivers using `nvcc --version`.
3. The build process is expected to take 1-2 hours. After that, you will be able to run Rango! 


**Note:** When creating the artifact, I encountered the following error while building the image:
```
docker: Error response from daemon: failed to create shim task: OCI runtime create failed: runc create failed: unable to start container process: error during container init: error running hook #0: error running hook: exit status 1, stdout: , stderr: Auto-detected mode as 'legacy'
nvidia-container-cli: mount error: failed to add device rules: unable to find any existing device filters attached to the cgroup: bpf_prog_query(BPF_CGROUP_DEVICE) failed: invalid argument: unknown.
``` 
To fix this error, I had to set `no-cgroups = true` in `/etc/nvidia-container-runtime/config.toml`.


## Usage
Once you have successfully created a docker image for this artifact, you can run Rango on theorems from CoqStoq!
First, you should spawn a container from the image you built:
```
docker run -it --rm --runtime=nvidia --gpus all rango /bin/bash
```
Once you are in the container, run `nvidia-smi` to ensure you have access to GPUs.


There are two main scripts in our artifact:
- `scripts/replicate.py`: This script takes a table name from the paper as a flag and re-tabulates the numbers in the table from 
raw cached proof search results. For figures and tables (tab1, fig2, fig3) that do not involve proof search, this command tabulates the numbers in the tables from 
scratch. 

  **For example:** ``scripts/replicate.py --tab1`` counts the number of proof steps, theorems, and repositories in the CoqStoq dataset.

- `scripts/run_thm.py`: This script runs any of the models appearing in the paper on any of the theorems that they were evaluated on in the paper. 
This script also has code to re-run all evaluations appearing in the paper, though doing so would entail running 50,000+ proof searches each with a 10 minute timeout. 
You can use this script by using one of its four subcommands: `info`, `preview`, `run`, `eval`.
  - `scripts/run_thm.py info` lists the model-ids of the models appearing in the paper. For example "rango" is the model id for Rango, and "no-lemma" is the model id for our ablation in table 4 where we run rango without retrieving lemmas. These model-ids are used in the `preview`, `run`, and `eval` commands. 

  - `scripts/run_thm.py preview <model_id> <split>`: Gives a sample of 50 theorem indices from CoqStoq on which the model was evaluated in the paper, whether or not
  the given model succeeded on those theorems, and how long it took the model to find their proofs. These theorem indices are used in the `run` command. `split` 
  must be one of "test" or "cutoff" - depending on if you are replicating a result from CoqStoq's testing split, or CoqStoq's cutoff split.  

    **For example:** `python3 scripts/run_thm.py preview rango test` shows the results (and theorem indices) of running Rango on the first 50 theorems from the CoqStoq test set. This is useful for selecting which individual theorems you would like to use to replicate Rango (i.e. proofs that Rango found reletively quickly would require less waiting time when replicating the result).

  - `scripts/run_thm.py run <model_id> <split> <thm_idx>`: Runs the given model on the given theorem from the given split. It also shows the original result 
  from the paper on running the given model on the given theorem. Note that due to Rango's stochastic algorithm, Rango might take shorter or longer to find a proof than it did in the original evaluation. It also might not find the same proof as it found in the evaluation, it might succeed where it previously failed, or it might fail where it previously succeeded. However, you will see that in general it takes a similar amount of time and finds similar proofs to those it found in the paper's evaluation. 

    **For example:** `python3 scripts/run_thm.py run rango test 5` runs Rango on the theorem with id 5 from the CoqStoq test split.
    It also outputs the 
  
  - `scipts/run_thm.py eval <model_id> <split>`: Runs an evaluation of the given model on the given split from scratch. Note that without proper parallelization (which is not implemented by this artifact), this command will take on the order of weeks to months to terminate. This command is obviously parallelizable, though how it is parallized depends on the experimentors particular cluster, which we don't make assumptions about in this artifact. 

    **For example:** `python3 scripts/run_thm.py eval rango test` evaluates Rango on the CoqStoq test split.

