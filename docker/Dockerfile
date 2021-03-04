FROM coqorg/coq:8.13.0-ocaml-4.11.1-flambda

## For some reason, coq starts with user "coq", not root
USER root

# Utilities
RUN apt-get update; \
    apt-get install -y vim less nano

# Welcome message
RUN echo '[ ! -z "$TERM" -a -r /etc/welcome ] && cat /etc/welcome' \
    >> /etc/bash.bashrc \
    ; echo -e "\
===================================================================\n\
= Artifact: Zooid: a DSL for Certified Multiparty Computation     =\n\
===================================================================\n\
\n\
PWD=/home/artifact/Zooid \n\
\n\
This directory contains the source code for our tool, as well as \n\
examples of protocols and certified processes. We scripts to guide \n\
running this artifact. Please find in README.md a more detailed  \n\
description. \n\
\n\
  * README.md  ............... Description of this artifact \n\
  * LICENSE  ................. MIT License \n\
  * run.sh  .................. Step-by-step tutorial/walkthrough \n\
  * theories ................. Zooid implementation and correctness proofs \n\
    |- theories/Tutorial.v ... Short tutorial on implementing Zooid procs \n\
  * runtime .................. OCaml runtime for executing processes \n\
  * scripts .................. Scripts for running the examples \n\
  * _CoqProject .............. Coq Project file for generating Makefile \n\
  * generateMakefile ......... Script to generate Makefile from _CoqProject \n\
  * doc ...................... Documentation for this project \n\
\n"\
    > /etc/welcome

_CoqProject  doc  generateMakefile  run.sh  runtime  scripts  theories

###############################################################################
# Artifact user

USER coq

###############################################################################
# Install dependencies

RUN opam update; \
    opam install -y coq-mathcomp-ssreflect.1.12.0 coq-mathcomp-finmap.1.5.1 coq-paco.4.0.4 lwt.5.4.0

###############################################################################
# Download artifact and build

COPY --chown=coq . Zooid

WORKDIR /home/coq/Zooid

RUN rm -rf .git* .circleci notes dist docker

# RUN ./scripts/buildall.sh

ENV TERM xterm-256color
CMD ["/bin/bash", "-l"]
