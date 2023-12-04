

ORIG_PATH:=$(abspath .)
RAW_DATA_LOC:=raw-data/coq-dataset
BUILD_LOC:=build-coq
REPOS_NAME:=repos
RAW_DATA_PROJECTS:=$(notdir $(realpath $(wildcard $(RAW_DATA_LOC)/$(REPOS_NAME)/*/)))
PROJECT_TARGETS:=$(addprefix $(BUILD_LOC)/$(REPOS_NAME)/, $(RAW_DATA_PROJECTS))

eval: $(PROJECT_TARGETS)
	echo "Done"

$(BUILD_LOC)/$(REPOS_NAME)/%: $(RAW_DATA_LOC)/$(REPOS_NAME)/%/
	python3 src/evaluation/compile_project.py $(RAW_DATA_LOC) $* $(BUILD_LOC)

clean:
	rm -rf $(BUILD_LOC) 
	find $(CORPUS_LOC) -name "*.vo" -delete
	find $(CORPUS_LOC) -name "valid_files.csv" -delete