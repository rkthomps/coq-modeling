FROM tensorflow/tensorflow:2.12.0-gpu
RUN apt-get -y update
RUN apt-get install -y vim
RUN add-apt-repository ppa:deadsnakes/ppa && \
	apt-get -y update && \
	apt-get install -y python3.10 python3.10-venv python3.10-dev
RUN curl -sS https://bootstrap.pypa.io/get-pip.py | python3.10
RUN apt-get install -y wget git
RUN wget https://github.com/ocaml/opam/releases/download/2.1.2/opam-2.1.2-x86_64-linux
RUN chmod +x opam-2.1.2-x86_64-linux
RUN mv opam-2.1.2-x86_64-linux /usr/bin/opam
RUN apt-get install -y libgmp-dev 
RUN apt-get -y install graphviz capnproto libcapnp-dev pkg-config libev-dev libxxhash-dev

RUN useradd -ms /bin/bash graph2tac
USER graph2tac
WORKDIR /home/graph2tac

RUN opam init --disable-sandboxing
RUN opam switch create tactician ocaml-base-compiler.4.12.1 --repos=custom-archive=git+https://github.com/LasseBlaauwbroek/custom-archive.git,coq-released=https://coq.inria.fr/opam/released,default
RUN opam switch tactician
RUN opam switch show
RUN opam pin add -y coq 8.11.dev
RUN opam install -y coq-serapi
RUN eval $(opam env) && opam install -y coq-graph2tac coq-tactician-stdlib
ENV PATH="$PATH:/home/graph2tac/.opam/tactician/bin:/home/graph2tac/.local/bin"
RUN tactician enable
RUN tactician inject

RUN python3.10 -m pip install graph2tac

RUN git clone https://github.com/HazardousPeach/coq_serapy.git
RUN cd coq_serapy && python3.10 -m pip install .

COPY requirements.txt /home/graph2tac/requirements.txt
RUN python3.10 -m pip install -r requirements.txt

ARG git_token
ENV GIT_ACCESS_TOKEN=$git_token
RUN git clone https://$GIT_ACCESS_TOKEN@github.com/Nfsaavedra/coq-modeling.git

WORKDIR /home/graph2tac/coq-modeling
RUN python3.10 -m pip install .

RUN git submodule set-url -- coqpyt https://github.com/sr-lab/coqpyt
RUN git submodule update --init coqpyt
WORKDIR /home/graph2tac/coq-modeling/coqpyt
RUN python3.10 -m pip install .

RUN mkdir /home/graph2tac/coq-modeling/tactician
RUN mkdir /home/graph2tac/coq-modeling/tactician/scripts
COPY scripts/tactician_graph2tac.py /home/graph2tac/coq-modeling/tactician/scripts/tactician.py

RUN mkdir /home/graph2tac/coq-modeling/raw-data && \
	mkdir /home/graph2tac/coq-modeling/raw-data/coq-dataset && \
	mkdir /home/graph2tac/coq-modeling/raw-data/coq-dataset/repos
WORKDIR /home/graph2tac/coq-modeling/slurm/example-jobs
COPY --chown=graph2tac modified-install-projects.sh /home/graph2tac/coq-modeling/slurm/example-jobs/install-projects.sh
RUN chmod +x install-projects.sh && ./install-projects.sh /home/graph2tac

COPY --chown=graph2tac scripts/generate_data_points_8_12.py /home/graph2tac/coq-modeling/tactician/scripts/generate_data_points_8_12.py
COPY --chown=graph2tac sentences.db /home/graph2tac/coq-modeling/raw-data/coq-dataset/sentences.db

WORKDIR /home/graph2tac/coq-modeling/tactician/scripts
COPY data_points /home/graph2tac/coq-modeling/raw-data/coq-dataset/data_points
RUN python3.10 generate_data_points_8_12.py
ENV PROTOCOL_BUFFERS_PYTHON_IMPLEMENTATION=python