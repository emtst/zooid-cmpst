# Certified MPST -- Zooid

This is the repo for MPST metatheory and Zooid a certified process descrition language.
It's implemented in the Coq proof assistant.

## Requirements

We recommend installing coq and its dependencies using OPAM, please
follow: [opam](https://opam.ocaml.org/) and
[opam's Coq repository](http://coq.io/opam/).

This development requires the following libraries:


| Dependency         | OPAM package Name      | Version |
|--------------------|------------------------|--------:|
| Coq                | coq                    |  8.11.2 |
| PaCo               | coq-paco               |   4.0.0 |
| MathComp/ssreflect | coq-mathcomp-ssreflect |  1.11.0 |
| MathComp/finmap    | coq-mathcomp-finmap    |   1.5.0 |


## Running the code

From this repo's directory run to build the proof and examples:
   `./generateMakefile && make`

After running the main make, the successful output should be similar to
like:

```
COQDEP VFILES
COQC theories/Forall.v
COQC theories/Atom.v
COQC theories/LNVar.v
COQC theories/AtomSets.v
COQC theories/Actions.v
COQC theories/Global.v
COQC theories/Local.v
COQC theories/Session.v
COQC theories/Projection.v
COQC theories/WellFormed.v
COQC theories/QProjection.v
COQC theories/TraceEquiv.v
COQC theories/Proc.v
Closed under the global context
Closed under the global context
COQC theories/Zooid.v
```

The last three lines confirm that the main theorems do not depend on
axioms or admitted lemmas, and Zooid contains all the definition of
the proof language and its examples.
