From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.MP.Atom.
Require Import MPST.MP.Role.
Require Import MPST.MP.Forall.
Require Import MPST.MP.LNVar.
Require Import MPST.MP.Global.
Require Import MPST.MP.Local.
Require Import MPST.MP.Actions.
Require Import MPST.MP.Projection.

Section TraceEquiv.

  Definition step_equiv G P :=
    forall a, exists G' P', step a G G' <-> lstep a P P'.

  Definition trace_equiv G P :=
    forall a, exists G' P', g_lts a G G' <-> l_lts a P P'.

  Theorem global_local_trequiv G :
    forall P,
    projection G == Some P ->
    trace_equiv (init G) ([::], P).
  Proof.
  Admitted.

End TraceEquiv.
