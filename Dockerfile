# ARG IMAGE_NAME
# FROM nvidia/cuda:12.4.1-runtime-ubuntu22.04 as base

ARG CUDA_VERSION
FROM nvidia/cuda:${CUDA_VERSION}-runtime-ubuntu22.04 as base

WORKDIR /app

RUN apt-get update && apt-get upgrade -y
RUN apt-get install -y build-essential
RUN apt-get install -y software-properties-common

ENV DEBIAN_FRONTEND noninteractive

RUN add-apt-repository ppa:deadsnakes/ppa
RUN apt install -y python3.11-dev
RUN apt install -y python3.11-venv
RUN apt install -y git

RUN mkdir /app/coq-modeling
WORKDIR /app/coq-modeling

COPY ./CoqStoq /app/coq-modeling/CoqStoq
WORKDIR /app/coq-modeling/CoqStoq
RUN /usr/bin/python3.11 -m venv venv
ENV PATH="/app/coq-modeling/CoqStoq/venv/bin:$PATH"

RUN pip3 install --no-cache-dir -e .

RUN apt install -y opam
RUN opam -y init
WORKDIR /app/coq-modeling/CoqStoq
RUN apt-get install -y libgmp-dev pkg-config
RUN opam switch import -y coqstoq.opam --switch=coqstoq --repos=default,coq-released=https://coq.inria.fr/opam/released
RUN opam switch set coqstoq

# # In place of 'eval opam env'
ENV OPAM_SWITCH_PREFIX='/root/.opam/coqstoq'
ENV CAML_LD_LIBRARY_PATH='/root/.opam/coqstoq/lib/stublibs:/root/.opam/coqstoq/lib/ocaml/stublibs:/root/.opam/coqstoq/lib/ocaml'
ENV OCAML_TOPLEVEL_PATH='/root/.opam/coqstoq/lib/toplevel'
ENV MANPATH='/root/.opam/coqstoq/man'
ENV PATH="/root/.opam/coqstoq/bin:$PATH"

RUN python3 -m pip install packaging 
RUN python3 coqstoq/build_projects.py 

WORKDIR /app/coq-modeling

COPY ./pyproject.toml /app/coq-modeling/pyproject.toml
COPY ./src /app/coq-modeling/src
COPY ./test /app/coq-modeling/test
COPY ./coqpyt /app/coq-modeling/coqpyt

RUN /usr/bin/python3.11 -m venv venv
ENV PATH="/app/coq-modeling/venv/bin:$PATH"

RUN pip3 install --no-cache-dir -e .

WORKDIR /app/coq-modeling/coqpyt
RUN pip3 install --no-cache-dir -e .

WORKDIR /app/coq-modeling/CoqStoq
RUN pip3 install --no-cache-dir -e .

WORKDIR /app/coq-modeling

COPY ./data /app/coq-modeling/data
COPY ./models /app/coq-modeling/models
COPY ./raw-data /app/coq-modeling/raw-data

RUN ln -s /app/coq-modeling/CoqStoq/test-repos raw-data/coqstoq-test/repos
RUN ln -s /app/coq-modeling/CoqStoq/val-repos raw-data/coqstoq-val/repos
RUN ln -s /app/coq-modeling/CoqStoq/cutoff-repos raw-data/coqstoq-cutoff/repos

COPY ./splits /app/coq-modeling/splits
COPY ./results /app/coq-modeling/results
COPY ./scripts /app/coq-modeling/scripts

COPY ./ARTIFACT.md /app/coq-modeling/ARTIFACT.md
COPY ./MAP.md /app/coq-modeling/MAP.md
COPY ./README.md /app/coq-modeling/README.md
COPY ./LICENSE /app/coq-modeling/LICENSE


ENV OPENAI_API_KEY=""
