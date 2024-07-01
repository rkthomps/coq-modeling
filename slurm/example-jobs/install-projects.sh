#!/bin/bash
#SBATCH -c 32
#SBATCH --mem=16384
#SBATCH -p cpu-preempt
#SBATCH -t 5:00:00
#SBATCH --mail-type=BEGIN,END,FAIL
#SBATCH -o slurm-install-projs-%j.out

HOME_DIR=/home/nfsaavedra/Projects
PROJECT_DIR=$HOME_DIR/coq-modeling
REPOS_DIR=$PROJECT_DIR/raw-data/coq-dataset/repos

opam pin add -y coq 8.18.0
opam repo add -y coq-released https://coq.inria.fr/opam/released

install() {
	project=$1
	if [ -d "$REPOS_DIR/coq-community-$project" ]; then
  		echo "Skipping $project"
		return
	fi

	echo "Processing $project"
	cd $REPOS_DIR
	opam install -y coq-$project
	git clone git@github.com:coq-community/$project coq-community-$project
	cd coq-community-$project
	make -j32
}

# Most of the coq-community installations can be done in the same way
install "reglang"
install "fourcolor"
install "math-classes"
install "sudoku"
install "bertrand"
install "stalmarck"
install "qarith-stern-brocot"
install "coqeal"
install "buchberger"
install "dblib"
install "hoare-tut"
install "huffman"
install "zorns-lemma"

# Annoying prefix
if [ -d "$REPOS_DIR/coq-community-coq-ext-lib" ]; then
	echo "Skipping coq-ext-lib"
else
	echo "Processing coq-ext-lib"
	cd $REPOS_DIR
	opam install -y coq-ext-lib
	git clone git@github.com:coq-community/coq-ext-lib coq-community-coq-ext-lib
	cd coq-community-coq-ext-lib
	make -j32
fi

# Contribs
if [ -d "$REPOS_DIR/thery-PolTac" ]; then
	echo "Skipping thery-PolTac"
else
	echo "Processing thery-PolTac"
	cd $REPOS_DIR
	git clone git@github.com:thery/PolTac thery-PolTac
	cd thery-PolTac
	make all
fi

# CompCert
if [ -d "$REPOS_DIR/AbsInt-CompCert" ]; then
	echo "Skipping CompCert"
else
	echo "Processing CompCert"
	cd $REPOS_DIR
	git clone git@github.com:AbsInt/CompCert AbsInt-CompCert
	cd AbsInt-CompCert
	./configure --ignore-coq-version --ignore-ocaml-version x86_64-linux
	make -j32
fi

# coq-contribs-zfc
if [ -d "$REPOS_DIR/coq-contribs-zfc" ]; then
	echo "Skipping coq-contribs-zfc"
else
	echo "Processing coq-contribs-zfc"
	cd $REPOS_DIR
	git clone git@github.com:coq-contribs/zfc.git coq-contribs-zfc
	cd coq-contribs-zfc
	make
fi
