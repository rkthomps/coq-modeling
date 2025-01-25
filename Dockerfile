ARG IMAGE_NAME
FROM nvidia/cuda:12.6.3-runtime-ubuntu24.04 as base

WORKDIR /app

RUN apt-get update && apt-get upgrade -y
RUN apt-get install -y build-essential
RUN apt-get install -y software-properties-common
RUN add-apt-repository ppa:deadsnakes/ppa
RUN apt install -y python3.11-dev
RUN apt install -y python3.11-venv
RUN apt install -y git

COPY . /app/coq-modeling

WORKDIR /app/coq-modeling

RUN /usr/bin/python3.11 -m venv venv
ENV PATH="/app/coq-modeling/venv/bin:$PATH"

RUN pip3 install --no-cache-dir -e .

WORKDIR /app/coq-modeling/coqpyt
RUN pip3 install --no-cache-dir -e .

WORKDIR /app/coq-modeling/CoqStoq
RUN pip3 install --no-cache-dir -e .

WORKDIR /app/coq-modeling

RUN ln -s /app/coq-modeling/CoqStoq/test-repos/ raw-data/coqstoq-test/repos
RUN ln -s /app/coq-modeling/CoqStoq/val-repos/ raw-data/coqstoq-val/repos
RUN ln -s /app/coq-modeling/CoqStoq/cutoff-repos/ raw-data/coqstoq-cutoff/repos
