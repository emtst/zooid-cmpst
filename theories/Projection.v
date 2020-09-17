From mathcomp.ssreflect Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Export MPST.Projection.IProject.
Require Export MPST.Projection.CProject.
Require Export MPST.Projection.QProject.
Require Export MPST.Projection.Correctness.

Definition Projection G P := eProject G P.1 /\ qProject G P.2.
