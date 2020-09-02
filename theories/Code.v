(* This file controls the extraction of code from the examples *)

From mathcomp Require Import all_ssreflect seq.
From mathcomp Require Import finmap.

From Paco Require Import paco paco2.

Require Import MPST.Actions.
Require Import MPST.AtomSets.
Require Import MPST.Forall.
Require Import MPST.Global.
Require Import MPST.Projection.
Require Import MPST.Local.
Require Import MPST.TraceEquiv.
Require Import MPST.Proc.
Require Import MPST.Zooid.
Require Import MPST.Examples.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Cd "./runtime/examples".


(* Extraction examples *)

Require Import Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Opaque eqn.
Opaque addn.
Opaque muln.
Opaque subn.
Opaque maxn.


(* pipeline example *)

Module  BOB (MP : ProcessMonad) : Process(MP).
  Module PE := ProcExtraction(MP).
  Definition proc := Eval compute in PE.extract_proc 0 (get_proc bob).
End BOB.

Cd "./pipeline".

Separate Extraction BOB.

Cd "..".



(* leave this at the end, it needs to stay in the same directory it started *)
Cd "../..".
