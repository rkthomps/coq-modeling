

ORIG_PATH:=$(abspath .)
#CORPUS_LOC:=raw-data/coq-dataset/repos
CORPUS_LOC:=foo
PROJECTS:=$(wildcard $(CORPUS_LOC)/*)

eval: build/compile
	echo $(abspath .)
	echo "Done"

build/compile: $(PROJECTS)
	cd coq-crawler; for f in $?; do python3 -c "from project import Project; Project(\"$(ORIG_PATH)/$$f)\")"; done
	mkdir -p build
	touch build/compile

clean:
	rm -rf build