#!/bin/bash
#SBATCH -c 32
#SBATCH --mem=16384
#SBATCH -p cpu-preempt
#SBATCH -t 5:00:00
#SBATCH --mail-type=BEGIN,END,FAIL
#SBATCH -o slurm-install-projs-%j.out

HOME_DIR=$1
PROJECT_DIR=$HOME_DIR/coq-modeling-g2t
REPOS_DIR=$PROJECT_DIR/raw-data/coq-dataset/repos

opam pin add -y coq 8.11.dev
opam repo add -y coq-released https://coq.inria.fr/opam/released

install() {
	project=$1
	version=$2
	if [ -d "$REPOS_DIR/coq-community-$project" ]; then
  		echo "Skipping $project"
		return
	fi

	echo "Processing $project"
	cd $REPOS_DIR
	git clone https://github.com/coq-community/$project.git coq-community-$project
	if [ $? != 0 ]; then
		exit 1
	fi
	cd coq-community-$project
	git checkout $version
	opam install -y coq-$project
	make -j32
}

# Most of the coq-community installations can be done in the same way
install "math-classes" "8.18.0"
install "reglang" "v1.1.3"
install "fourcolor" "v1.2.5"
install "sudoku" "8.16.0"
install "bertrand" "ba9a47f9773adcace400ef70ce49e1ee627aa557"
install "stalmarck" "v8.12.0"
install "qarith-stern-brocot" "v8.13.0"
install "coqeal" "1.1.0"
install "buchberger" "v8.14.0"
install "dblib" "25469872c0ba99b046f7e5b8608205eeea5ac077"
install "hoare-tut" "66dfb255c9e8bb49269d83b3577b285288f39928"
install "huffman" "adfb872b68aeba2426440ee6cbb73fa698ce17fc"
install "zorns-lemma" "aaf46b0c5f7857ce9211cbaaf36f184ca810e0e8"

# Annoying prefix
if [ -d "$REPOS_DIR/coq-community-coq-ext-lib" ]; then
	echo "Skipping coq-ext-lib"
else
	echo "Processing coq-ext-lib"
	cd $REPOS_DIR
	opam install -y coq-ext-lib
	git clone https://github.com/coq-community/coq-ext-lib.git coq-community-coq-ext-lib
	if [ $? != 0 ]; then
		exit 1
	fi
	cd coq-community-coq-ext-lib
	git checkout b1fa2800a867df12eaced8ad324a04c2ada12a5a
	make -j32
fi

# Contribs
if [ -d "$REPOS_DIR/thery-PolTac" ]; then
	echo "Skipping thery-PolTac"
else
	echo "Processing thery-PolTac"
	cd $REPOS_DIR
	git clone https://github.com/thery/PolTac.git thery-PolTac
	if [ $? != 0 ]; then
		exit 1
	fi
	cd thery-PolTac
	git checkout v8.12
	make all
fi

# CompCert
if [ -d "$REPOS_DIR/AbsInt-CompCert" ]; then
	echo "Skipping CompCert"
else
	echo "Processing CompCert"
	cd $REPOS_DIR
	git clone https://github.com/AbsInt/CompCert.git AbsInt-CompCert
	if [ $? != 0 ]; then
		exit 1
	fi
	cd AbsInt-CompCert
	git checkout v3.8
	./configure --ignore-coq-version --ignore-ocaml-version x86_64-linux
	make -j32
fi

# coq-contribs-zfc
if [ -d "$REPOS_DIR/coq-contribs-zfc" ]; then
	echo "Skipping coq-contribs-zfc"
else
	echo "Processing coq-contribs-zfc"
	cd $REPOS_DIR
	git clone https://github.com/coq-contribs/zfc.git coq-contribs-zfc
	if [ $? != 0 ]; then
		exit 1
	fi
	cd coq-contribs-zfc
	make
fi
