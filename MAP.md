# Map of Source Code for Rango

## Introduction
This map describes where the various aspects of Rango are implemented in its source code. 
Note that the pipeline for creating and evaluating Rango has the following steps: 
- **Data Preprocessing**: 
- **Training**
- **Inference**
- **Evaluation**

We describe the source code implementing each of these steps below. 

### Data Preprocessing
The data processing phase of the pipeline has three main components:
- **Extraction**: 
We must gather the Coq-Level information from our corpus before we can use it to train LLMs. 
This means collecting proofs, premises, proof states, etc. from raw Coq Repositories. 
The file [`src/data_management/create_file_data_point.py`](src/data_management/create_file_data_point.py) creates an internal `DatasetFile` object for the given Coq file. 
For convenience, one can create data points for en entire repository using [`scripts/create_repo_data_points.py`](scripts/create_repo_data_points.py).

- **Splitting**: 
  Before we finetune LLMs to generate proofs, we split the dataset into a training / testing / validation split. 
  The logic for splitting the data into these splits is contained in [`src/data_management/splits.py`](src/data_management/splits.py).

- **Preprocessing**
  Before we finetune Rango, we put each proof step into an "LLM-Friendly" format. 
  That is, we represent each example using an internal data structure called an [`LmExample`](src/tactic_gen/lm_example.py). 
  Note that this conversion requires performing proof and lemma retrieval at each proof step.  
  - The primary file implementing proof retrieval is [`src/proof_retrieval/proof_retriever.py`](src/proof_retrieval/proof_retriever.py). 
  - The primary file implementing lemma retrieval is [`src/premise_selection/premise_client.py`](src/premise_selection/premise_client.py). 


  Proof steps in our repository are converted to `LmExample`s using [`src/data_management/create_dataset.py`](src/data_management/create_dataset.py).
  Running this command requires access to a slurm cluster, and requires a configuration file that gets loaded into a [`LmDatasetConf`](src/data_management/dataset_utils.py) object.


### Training
There are two parts of the training process: collating examples, and running training steps.
These two parts correspond to two files in the source.
Note that we fine-tuned Rango using 4 Nvidia A100 GPUs for around 2 days. 
- [`src/tactic_gen/tactic_data.py`](src/tactic_gen/tactic_data.py): Contains logic for formatting prompts and targets for the LLM at the token-by-token level.
- [`src/tactic_gen/train_decoder.py`](src/tactic_gen/train_decoder.py): Contains logic for actually fine-tuning the LLM.  


### Inference
The main method for conducting inference using Rango is `run_proof` which is contained in [`src/model_deployment/prove.py`](src/model_deployment/prove.py). 
To run a model on a theorem, one must specify the following (among other things):
- The theorem (as an `EvalTheorem` theorem in the CoqStoq dataset).
- The model.
- The search procedure. The search procedure can be one of the following:
  - Rollout search: implemented in [`src/model_deployment/straight_line_searcher.py`](src/model_deployment/straight_line_searcher.py).
  - Best-first search: implemented in [`src/model_deployment/classicial_searcher.py`](src/model_deployment/classical_searcher.py).
- Note that [`scripts/run_thm.py`](scripts/run_thm.py) provides a nice interface for running inference with Rango.

### Evaluation
Note that while [`scripts/run_thm.py`](scripts/run_thm.py) gives a single-threaded evaluation of Rango, an equivalent, but parallelized evaluation of Rango is emplemented using [`src/evaluation/eval.py`](src/evaluation/eval.py).
This script assumes that you are running the evaluation on a slurm cluster. 
The evaluation is straight forward: it simply runs the given model, using the given search procedure, on a set of theorems from CoqStoq. It expects a configuration file that is loaded into a [`EvalConf`](src/evaluation/eval_utils.py) object.



## Questions: 
If you have further questions, please feel free to email Kyle Thompson at r7thompson@ucsd.edu.

