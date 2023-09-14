# coq-modeling
Language models for Coq based on data collected from the coq lsp. 

## Setup
- **Install Project:** Change to project directory and run `python3 -m pip install --editable .`

## Dowloading and Partitioning Data
- Download ~40% of coq data scraped from GitHub [here](https://drive.google.com/file/d/17b85sftlgmQxqxFXZ7JPUOAfazaTROUw/view?usp=sharing). For purposes of this document, assume the raw data is downloaded to "/raw/data/location"
- Partition the raw data into training, validation and testing with\
  `python3 src/data_management/split_raw_data.py --assignment assignment.json /raw/data/location`.\
  Alternatively, you can create your own splits with\
  `python3 src/data_management/split_raw_data.py --train_prop 0.8 --val_prop 0.1 --test_prop 0.1 /raw/data/location`.
- After running this script, there should be a new directory called "/raw/data/location-split" containing the subdirectories "train", "val", "test". 

## Creating Tactic Generation Training Data
Since we use Language Models to predict tactics, both the input and target of our examples are strings. The interface [LmExample](src/data_management/lm_example.py) represents such an example. To define how input and target strings are composed, create a subclass of LmExample. The subclass simply needs to define how to create a list of examples given a [DatasetFile](src/data_management/dataset_file.py) object. A DatasetFile object is just a representation of the json-format of the raw data. 

Once you have composed your LmExample subclass, you can use the file [create_lm_dataset.py](src/data_management/create_lm_dataset.py) to convert the raw data into a dataset of examples. 
- First, if you created a new subclass of LmExample, give it an alias and add it to the dictionary `EXAMPLE_FORMATS`. For purposes of this document, assume we have a subclass of LmExample called BasicLmExample. We would add `"basic": BasicLmExample"` to the `EXAMPLE_FORMATS` dictionary.
- Then, you can simply run the script\
  `python3 src/data_management/create_lm_dataset.py /raw/data/location-split /processed/data/location basic`. As a result, you should see a new directory named "/processed/data/location" with the files "train-shuffled.jsonl", "val-shuffled.jsonl", and "test-shuffled.jsonl". Each line of one of the .jsonl files represents one example. The examples are shuffled within their respective splits.

## Finetuning Code Llama
To finetune Code Llama, you can run `CUDA_VISIBLE_DEVICES=0 python3 train_codellama.py src/tactic_gen/confs/codellama_basic.yaml`. The value of `CUDA_VISIBLE_DEVICES` indicates the machine to be used for training. Currently, only single-gpu training is supported. You can configure the training by providing a .yaml config file. The file [codellama_basic.yaml](src/tactic_gen/confs/codellama_basic.yaml) is an example. 
