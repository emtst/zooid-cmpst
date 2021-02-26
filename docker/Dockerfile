FROM coqorg/coq:8.10

# Welcome message
RUN echo '[ ! -z "$TERM" -a -r /etc/welcome ] && cat /etc/welcome' \
    >> /etc/bash.bashrc \
    ; echo "\
===================================================================\n\
= Artifact: Zooid: a DSL for Certified Multiparty Computation     =\n\
===================================================================\n\
\n\
This is the artifact for the paper 'CAMP: Cost-Aware Multiparty \n\
Session Protocols' .\n\
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

# Add artifact user
RUN useradd -ms /bin/bash artifact

###############################################################################
# Install dependencies

RUN opam install -y coq-mathcomp-ssreflect \
    opam install -y coq-mathcomp-finmap \
    opam install -y coq-paco \


###############################################################################
# Download artifact and build

RUN git clone git@github.com:emtst/cmpst.git Zooid \
    cd artifact \
    ./generateMakefile \
    make \

WORKDIR /home/artifact/Zooid
ENV TERM xterm-256color

CMD ["/bin/bash", "-l"]
