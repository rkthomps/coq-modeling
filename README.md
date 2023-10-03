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
- **Install Project:** Change to project directory and run `python3 -m pip install --editable .`

## Dowloading and Partitioning Data
- Download ~40% of coq data scraped from GitHub [here](https://drive.google.com/file/d/17b85sftlgmQxqxFXZ7JPUOAfazaTROUw/view?usp=sharing). For purposes of this document, assume the raw data is downloaded to "/raw/data/location"
- Partition the raw data into training, validation and testing with\
  `python3 src/data_management/split_raw_data.py --assignment assignment.json /raw/data/location`.\
  Alternatively, you can create your own splits with\
  `python3 src/data_management/split_raw_data.py --train_prop 0.8 --val_prop 0.1 --test_prop 0.1 /raw/data/location`.
- After running this script, there should be a new directory called "/raw/data/location-split" containing the subdirectories "train", "val", "test".

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

## Creating Tactic Generation Training Data
Since we use Language Models to predict tactics, both the input and target of our examples are strings. The interface [LmExample](src/data_management/lm_example.py) represents such an example. To define how input and target strings are composed, create a subclass of LmExample. The subclass simply needs to define how to create a list of examples given a [DatasetFile](src/data_management/dataset_file.py) object and a [wrapper](src/model_deployment/premise_model_wrapper.py) for a Premise selection model . A DatasetFile object is just a representation of the json-format of the raw data. 

Once you have composed your LmExample subclass, you can use the file [create_lm_dataset.py](src/data_management/create_lm_dataset.py) to convert the raw data into a dataset of examples. 
- First, if you created a new subclass of LmExample, give it an alias via `get_alias: unit -> str` and add it to the `LMEXAMPLE_ALIASES` dictionary.
- Then, you can simply run the script\
  `python3 src/data_management/create_lm_dataset.py src/data_management/tactic-confs/premise_tactic.yaml`. Note, [premise_tactic.yaml](src/data_management/tactic-confs/premise_tactic.yaml) is a configuration file. It can and should be replaced with a custom config file. As a result, you should see a new directory named "/processed/data/location" with the files "train-shuffled.jsonl", "val-shuffled.jsonl", and "test-shuffled.jsonl". Each line of one of the .jsonl files represents one example. The examples are shuffled within their respective splits.


## Finetuning Code Llama
To finetune Code Llama, you can run\
`CUDA_VISIBLE_DEVICES=0 python3 train_codellama.py src/tactic_gen/confs/codellama_basic.yaml`.\
The value of `CUDA_VISIBLE_DEVICES` indicates the machine to be used for training. Currently, only single-gpu training is supported. You can configure the training by providing a .yaml config file. The file [codellama_basic.yaml](src/tactic_gen/confs/codellama_basic.yaml) is an example. 

## Evaluation
To evaluate 
- **Compiling Corpus**
  - Each directory in "/raw/data/location" has three files - "steps.jsonl", "file_context.jsonl", and "<file>.v". Our first step is extracting the heirarchy of coq files from the
    flat directory structure of "/raw/data/location". We accomplish this by:\
    `python3 src/evaluation/impose_file_hierarchy /raw/data/location /raw/data/hierarchy`\
    As a result, we will have a hierarchy of coq files rooted at "/raw/data/hierarchy"
  - To compile the files of "/raw/data/hierarchy", simply run\
    `python3 src/evaluation/compile_corpus.py /raw/data/hierarchy [-n <num processes>]`\
    This will compile all coq files in the hierarchy. `num processes` indicates what to pass to the `-j` option of `make`.
  - _I was able to compile 2246 of the 2593 files this way. I am still unsure why not all files compile._
- **Running Evaluation**
  - Run evaluation on a hold-out set of theorems with\
    `python3 src/evaluation/evaluate.py src/evaluation/confs/codellama.yaml`\
    Note, [codellama.yaml](src/evaluation/confs/codellama.yaml) is a configuration file, and can be replaced with any .yaml file of the same format. 
