

# Compile Constants
ORIG_PATH:=$(abspath .)
BUILD_LOC:=build-coq
REPOS_NAME:=repos
RAW_DATA_PROJECTS:=$(notdir $(realpath $(wildcard $(RAW_DATA_LOC)/$(REPOS_NAME)/*/)))
PROJECT_TARGETS:=$(addsuffix /, $(addprefix $(BUILD_LOC)/$(REPOS_NAME)/, $(RAW_DATA_PROJECTS)))

#CLINE ARGS
RAW_DATA_LOC?=raw-data/coq-dataset

eval: 
	if [ -z $(EVAL_CONF_LOC) ] 
	then 
		echo "Please provide eval configuration file via EVAL_CONF_LOC env var."
	else
		python3 




compile: $(PROJECT_TARGETS)
	echo "Done"

$(BUILD_LOC)/$(REPOS_NAME)/%/: $(RAW_DATA_LOC)/$(REPOS_NAME)/%/
	python3 src/evaluation/compile_project.py $(RAW_DATA_LOC) $* $(BUILD_LOC)


clean:
	rm -rf $(BUILD_LOC) 
	find $(CORPUS_LOC) -name "*.vo" -delete
	find $(CORPUS_LOC) -name "valid_files.csv" -delete