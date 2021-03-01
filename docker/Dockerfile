FROM coqorg/coq:8.13.0-ocaml-4.11.1-flambda

## For some reason, coq starts with user "coq", not root
USER root

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
  * README.md  ............. Description of this artifact \n\
  * LICENSE  ............... BSD-3 License for our code \n\
  * run.sh  ................ Step-by-step execution of this artifact \n\
  * theories ............... Coq implementation and correctness proofs for Zooid \n\
  * runtime ................ OCaml runtime for executing processes \n\
\n"\
    > /etc/welcome

###############################################################################
# Artifact user

USER coq

###############################################################################
# Install dependencies

RUN opam update; \
    opam install -y coq-mathcomp-ssreflect coq-mathcomp-finmap coq-paco lwt

###############################################################################
# Download artifact and build

COPY --chown=coq . Zooid

WORKDIR /home/coq/Zooid

RUN rm -rf .git* .circleci

RUN ./scripts/buildall.sh

ENV TERM xterm-256color
CMD ["/bin/bash", "-l"]
