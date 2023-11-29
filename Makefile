

ORIG_PATH:=$(abspath .)
CORPUS_LOC:=raw-data/coq-dataset/repos
PROJECT_TARGETS:=$(addprefix build/, $(wildcard $(CORPUS_LOC)/*/))

eval: $(PROJECT_TARGETS)
	echo "Done"

build/$(CORPUS_LOC)/%/: $(CORPUS_LOC)/%/
	echo $<
	cd coq-crawler; python3 -c "from project import Project; Project(\"$(ORIG_PATH)/$<\")" 
	mkdir -p $(dir $@)
	touch $@

clean:
	rm -rf build
	find $(CORPUS_LOC) -name "*.vo" -delete