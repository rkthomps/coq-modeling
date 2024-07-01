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

ARG display
RUN useradd -ms /bin/bash graph2tac
USER graph2tac
WORKDIR /home/graph2tac
ENV DISPLAY=$display
VOLUME /tmp/.X11-unix /tmp/.X11-unix
VOLUME .docker.xauth /home/graph2tac/.docker.xauth
ENV XAUTHORITY=/home/graph2tac/.docker.xauth

RUN opam init --disable-sandboxing
RUN opam switch create tactician ocaml-base-compiler.4.12.1 --repos=custom-archive=git+https://github.com/LasseBlaauwbroek/custom-archive.git,coq-released=https://coq.inria.fr/opam/released,default
RUN opam switch tactician
RUN opam switch show
RUN opam install -y coq-serapi
RUN eval $(opam env) && opam install -y coq-graph2tac coq-tactician-stdlib
ENV PATH="$PATH:/home/graph2tac/.opam/tactician/bin:/home/graph2tac/.local/bin"
RUN tactician enable
RUN tactician inject

RUN python3.10 -m pip install graph2tac

RUN git clone https://github.com/HazardousPeach/coq_serapy.git
RUN cd coq_serapy && python3.10 -m pip install .
