# Certified MPST -- Zooid --

This is the repo for MPST metatheory and Zooid a certified process descrition language.
It's implemented in the Coq proof assistant.

## Getting Started

In this section, we outline how to access and run the artifact. We
also introduce to the layout of the development and how to build the
system on your own.

### Obtain the artifact (Docker image hosted on Zenodo)

We provide a [Docker image](https://??) with all the necessary
dependencies. The following steps assume a Unix environment with
Docker properly installed. Other platforms supported by docker will
have analogous ways to import and handle the image. For more
information on docker itself refer to the documentation
[here.](https://docs.docker.com/)

Ensure that the docker Daemon is running. Load the image (using `sudo`
if necessary):

```bash
$ docker load < zooid-cmpst.tar.gz
````

You should see the following as output after the last operation:

```bash
Loaded image: zooid-cmpst
```

***Alternatively***, you can build the Docker image from source:

```bash
$ git clone --recursive \
	https://github.com/emtst/zooid-cmpst
$ cd cmpst/docker
$ ./buildimage.sh
```

### Running the examples

Once the Docker image has been loaded in your computer you can run it
with the following command:

```bash
$ docker run --rm -it zooid-cmpst
```

This contains an 'interactive' demo for some of the examples
implemented in Zooid. To execute the tutorial just run the following
command from the top level directory of the repository.

```bash
$ ./run.sh
```

## Running the code without the docker container

This sectiond describes the requirements to configure your environment
to run Zooid and the Coq developement natively without using docker.


## Requirements

We recommend installing coq and its dependencies using OPAM, please
follow: [opam](https://opam.ocaml.org/) and
[Coq's opam repository](http://coq.io/opam/).

This development requires the following libraries:


| Dependency         | OPAM package Name      | Version |
|--------------------|------------------------|--------:|
| Coq                | coq                    |    8.13 |
| PaCo               | coq-paco               |   4.0.4 |
| MathComp/ssreflect | coq-mathcomp-ssreflect |  1.12.0 |
| MathComp/finmap    | coq-mathcomp-finmap    |   1.5.1 |
| Ocaml              | ocaml                  |  4.11.1 |
| LWT                | lwt                    |   5.4.0 |
| Dune               | dune                   |   2.8.2 |


## Running the code

From this repo's directory run to build the proof and examples:
   `./generateMakefile && make`

After running the main make, the successful output should be similar to:

```
COQDEP VFILES
COQC theories/Common/Forall.v
COQC theories/Common/Member.v
COQC theories/Common/AtomSets.v
COQC theories/Common/Actions.v
COQC theories/Common/Queue.v
COQC theories/Common/Alt.v
COQC theories/Common.v
COQC theories/Global/Tree.v
COQC theories/Global/Semantics.v
COQC theories/Global/Syntax.v
COQC theories/Global/Unravel.v
COQC theories/Global.v
COQC theories/Local/Syntax.v
COQC theories/Local/Tree.v
COQC theories/Local/Unravel.v
COQC theories/Local/Semantics.v
COQC theories/Local.v
COQC theories/Session/Syntax.v
COQC theories/Session.v
COQC theories/Projection/IProject.v
COQC theories/Projection/CProject.v
COQC theories/Projection/QProject.v
COQC theories/Projection/PartialProj.v
COQC theories/Projection/Correctness.v
COQC theories/Projection/Compat.v
COQC theories/Projection.v
COQC theories/TraceEquiv.v
Closed under the global context
COQC theories/Proc.v
COQC theories/Zooid.v
COQC theories/Examples.v
COQC theories/Code.v
```

`Closed under the global context` denote that the final proof does not
depend on axioms or admitted lemmas.

## Building the coq proof and examples

To compile all the Coq and runtime OCaml code simply run:
```
./scripts/buildAll.sh
```

This command builds the whole system, once it is successfully compiled
the different examples can be run with the commands in the following
section.

## Run the examples

**Remark:** The underlying transport uses TCP/IP sockets. Running two
consecutive examples that use the same port number may cause an error:
```
Fatal error: exception Unix.Unix_error(Unix.EADDRINUSE, "bind", "")
```
After the necessary waiting time, the examples will run again without an error.


All the examples are implemented using Zooid and are in the file
`theories/Examples.v`. Each example in that file starts with a comment
with the same title as the following sections:

### Calculator Example
This first example is an interactive calculator example. Run it with:
```
./scripts/runCalculator.sh
```

Note that it uses Ocaml functions to interact over the console.


### PingPong Example

PingPong server and 5 clients. You can run the server against each of
the clients.

```
./scripts/runPingPong0.sh
./scripts/runPingPong1.sh
./scripts/runPingPong2.sh
./scripts/runPingPong3.sh
./scripts/runPingPong4.sh
```

Note that the implementation of client number 1 is sending pings for
ever so this protocol never terminates, use Ctrl + C to end it. Notice
that depending on your OS, the TCP/IP sockets may not have been
released immediately after you kill the program, so you may need to
wait for a couple of minutes before being able to run the other
examples.

###  Pipeline Example

This will run the protocol on a stream of random numbers and double
and print the result.

```
./scripts/runPipeline.sh
```

Note that the pipeline protocol never terminates, use Ctrl + C to end
it. Notice that depending on your OS, the TCP/IP sockets may not have
been released immediately after you kill the program, so you may need
to wait for a couple of minutes before being able to run the other
examples.


### Two-buyer Example

This example illustrates the two buyer protocol as discussed on the
paper.

```
./scripts/runTwoBuyer.sh
```
