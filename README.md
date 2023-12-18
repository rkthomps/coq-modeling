# coq-modeling
Language models for Coq based on data collected from the coq lsp. 

## Setup
- **Install Dependencies:**
    - Install repo:
      - `git clone --recurse-submodules https://github.com/rkthomps/coq-modeling`
    - Install opam (Ocaml package manager):
      - `sudo apt-get update && sudo apt-get install opam`.
      - `opam init`
      - `eval $(opam env --switch=default)`
    - Install coq-lsp:
      - `opam install coq-lsp`
    - You must have a cuda compiler. Determine how to install `nvcc` on your machine.
    - You must have a development version of python 3.10+ installed. 
- **Install Project:** Change to project directory and run `python3 -m pip install --editable .`

## Dowloading and Partitioning Data
The data currently exists on "inesc.id.pt" machines & [google drive](https://drive.google.com/drive/folders/12fruVfOomVO9pnJSN1T8CnG4ci95CdL2?usp=drive_link). The dataset has two parts: 
- Data-points (preprocessed data)
- Raw coq files
For training tasks, the data-points segment of the dataset is sufficient.
For evaluation tasks, the raw coq files segment of the dataset is sufficient.



## Creating Tactic Generation Training Data
Since we use Language Models to predict tactics, both the input and target of our examples are strings. The interface [LmExample](src/data_management/lm_example.py) represents such an example. To define how input and target strings are composed, create a `LmFormatter`. The subclass defines how to get a single (str -> str) training example from a single proof step. 

You can use the file [create_lm_dataset.py](src/data_management/create_lm_dataset.py) to convert the raw data into a dataset of examples. 
- This creates a dataset from a configuration file. You can use [random-sample-basic.yaml](src/data_management/tactic-confs/random-sample-basic.yaml) as a reference. Simply run the command `python3 src/data_management/create_lm_dataset.py -n 8 src/data_management/tactic-confs/random-sample-basic.yaml`. Note, [premise_tactic.yaml](src/data_management/tactic-confs/premise_tactic.yaml) is a configuration file. It can and should be replaced with a custom config file. As a result, you should see a new directory named "/processed/data/location" with the files "train-deduplicated-shuffled.jsonl", "val-deduplicated-shuffled.jsonl", and "test-deduplicated-shuffled.jsonl". Each line of one of the .jsonl files represents one example. The examples are shuffled and deduplicated within their respective splits.

## Finetuning Code Llama
To finetune Code Llama, you can run\
`torchrun --nproc-per-node=4 src/tactic_gen/train_codellama.py src/tactic_gen/confs/test.yaml`.\
The value of `--include` indicates the machines to be used for training. You can configure the training by providing a .yaml config file. The file [codellama_basic.yaml](src/tactic_gen/confs/codellama_basic.yaml) is an example.

## Creating Premise Selection Training Data
A training example for premise selection is associated with a single premise used in a single tactic. The example also contains a number of "negative premises" - premises that were not used in the tactic. These negative premises may be "in-file" negatives - premises from the same file as the proof, or "out-of-file" negatives - premises from a dependency of the proof. You can mine a premise selection dataset with\
`python3 src/data_management/create_premise_dataset.py src/data_management/premise-confs/premise_basic.yaml`\
where [premise_basic.yaml](src/data_management/premise_basic.yaml) is a configuration file for creating the premise selection dataset.

## Training a Premise Selection Model
You can train a premise selection model using [Pytorch Lightning](https://lightning.ai/). Specifically, run\
`CUDA_VISIBLE_DEVICES=4 python3 src/premise_selection/main.py fit -c src/premise_selection/confs/premise_train_basic.yaml`\
where [premise_train_basic.yaml](src/premise_selection/confs/premise_train_basic.yaml) is configuration file for training and can be substituted with a custom configuration file. 
**Acknowledgement:** Our premise selection model and its integration is heavily inspired by the great work on [LeanDojo](https://leandojo.org/).

## Evaluating Your Premise Selection Model
You can evaluate the premise selection model with\
`CUDA_VISIBLE_DEVICES=4 python3 src/premise_selection/evaluate.py /path/to/model/checkpoint /raw/data/location-split val`\
to evaluate a model saved to checkpoint "/path/to/model/checkpoint" on validation data from "/raw/data/location-split". Alternatively you could evaluate on "train" or "test" splits. 
 

## Evaluation
To evaluate a tactic prediction model, you need to ensure that you have a compiled corpus of coq files on your machine. 
To compile the corpus of coq files, run `make`. **TODO: make should take an argument specifying the location of of the corpus and an eval config**

- **Running Evaluation**
  - Run evaluation on a hold-out set of theorems with\
    `python3 src/evaluation/evaluate.py src/evaluation/confs/eval.yaml`\
    Note, [eval.yaml](src/evaluation/confs/eval.yaml) is a configuration file, and can be replaced with any .yaml file of the same format. 
