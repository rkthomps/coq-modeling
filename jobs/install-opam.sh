#!/bin/bash
#SBATCH -c 6
#SBATCH --mem=8192
#SBATCH -p cpu 
#SBATCH -t 02:00:00
#SBATCH --mail-type=BEGIN,END,FAIL

rm -rf ~/.opam
module load opam/2.1.2
opam init -y
mv ~/.opam /work/pi_brun_umass_edu/kthompson/.opam 
