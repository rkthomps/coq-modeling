# Rango
Rango is a proof synthesis tool for the Coq theorem prover.
Rango uses _retrieval augmentation_ to adapt to its environment.
This repository contains the code required for:
- Processing data to train Rango, proof retrievers and lemma retrievers
- Training Rango, proof retrievers and lemma retrievers
- Running Rango on proofs in CoqHub
- Evaluating Rango on CoqHub's testing set

## Setup
- **Install Dependencies:**
    - Install repo:
      - `git clone --recurse-submodules https://github.com/rkthomps/coq-modeling`
      - `pip3 install -e .`
      - `cd coqpyt`
      - `pip3 install .`
        
    - Install opam (Ocaml package manager):
      - `sudo apt-get update && sudo apt-get install opam`.
      - `opam init`
      - `eval $(opam env --switch=default)`
     
    - Install Coq:
      - `opam pin add coq 8.18.0`
        
    - Install coq-lsp:
      - `opam install coq-lsp`

