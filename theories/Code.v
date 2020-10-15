(* This file controls the extraction of code from the examples *)

From mathcomp Require Import all_ssreflect seq.
From mathcomp Require Import finmap.

From Paco Require Import paco paco2.

Require Import MPST.Common.
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


Cd "./runtime/examples/generated".


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

Module  ALICE (MP : ProcessMonad) : PROCESS_FUNCTOR(MP).
  Module PE := ProcExtraction(MP).
  Module PM := MP.
  Definition proc := Eval compute in PE.extract_proc 0 (get_proc alice).
End ALICE.

Module  BOB (MP : ProcessMonad) : PROCESS_FUNCTOR(MP).
  Module PE := ProcExtraction(MP).
  Module PM := MP.
  Definition proc := Eval compute in PE.extract_proc 0 (get_proc bob).
End BOB.

Module  CAROL (MP : ProcessMonad) : PROCESS_FUNCTOR(MP).
  Module PE := ProcExtraction(MP).
  Module PM := MP.
  Definition proc := Eval compute in PE.extract_proc 0 (get_proc carol).
End CAROL.

(* ping pong example *)

Module  PPSERVER (MP : ProcessMonad) : PROCESS_FUNCTOR(MP).
  Module PE := ProcExtraction(MP).
  Module PM := MP.
  Definition proc := Eval compute in PE.extract_proc 0 (get_proc ping_pong_server).
End PPSERVER.

(* never pings, justs quits *)
Module  PPCLIENT0 (MP : ProcessMonad) : PROCESS_FUNCTOR(MP).
  Module PE := ProcExtraction(MP).
  Module PM := MP.
  Definition proc := Eval compute in PE.extract_proc 0 (get_proc ping_pong_client0).
End PPCLIENT0.

(* always pings, never quits *)
Module  PPCLIENT1 (MP : ProcessMonad) : PROCESS_FUNCTOR(MP).
  Module PE := ProcExtraction(MP).
  Module PM := MP.
  Definition proc := Eval compute in PE.extract_proc 0 (get_proc ping_pong_client1).
End PPCLIENT1.

(* confused, similar to 0? *)
Module  PPCLIENT2 (MP : ProcessMonad) : PROCESS_FUNCTOR(MP).
  Module PE := ProcExtraction(MP).
  Module PM := MP.
  Definition proc := Eval compute in PE.extract_proc 0 (get_proc (projT2 ping_pong_client2)).
End PPCLIENT2.

(* pings 2 times and then quits *)
Module  PPCLIENT3 (MP : ProcessMonad) : PROCESS_FUNCTOR(MP).
  Module PE := ProcExtraction(MP).
  Module PM := MP.
  Definition proc := Eval compute in PE.extract_proc 0 (get_proc (projT2 (ping_pong_client3 2))).
End PPCLIENT3.

(* pings until a pong provides more than 3 *)
Module  PPCLIENT4 (MP : ProcessMonad) : PROCESS_FUNCTOR(MP).
  Module PE := ProcExtraction(MP).
  Module PM := MP.
  Definition proc := Eval compute in PE.extract_proc 0 (get_proc (projT2 ping_pong_client4)).
End PPCLIENT4.

(* two buyer example *)

Module  SELLER (MP : ProcessMonad) : PROCESS_FUNCTOR(MP).
  Module PE := ProcExtraction(MP).
  Module PM := MP.
  Definition proc := Eval compute in PE.extract_proc 0 (get_proc seller_proc).
End SELLER.

Module  BUYERA (MP : ProcessMonad) : PROCESS_FUNCTOR(MP).
  Module PE := ProcExtraction(MP).
  Module PM := MP.
  Definition proc := Eval compute in PE.extract_proc 0 (get_proc buyerA).
End BUYERA.

Module  BUYERB (MP : ProcessMonad) : PROCESS_FUNCTOR(MP).
  Module PE := ProcExtraction(MP).
  Module PM := MP.
  Definition proc := Eval compute in PE.extract_proc 0 (get_proc buyerB).
End BUYERB.


(* the calculator example *)

Module AServer (MP : ProcessMonad) : PROCESS_FUNCTOR(MP).
  Module PE := ProcExtraction(MP).
  Module PM := MP.
  Definition proc := Eval simpl in PE.extract_proc 0 (get_proc AServer).
End AServer.

Module AClient (MP : ProcessMonad) : PROCESS_FUNCTOR(MP).
  Module PE := ProcExtraction(MP).
  Module PM := MP.
  Definition proc := Eval simpl in PE.extract_proc 0 (get_proc AClient).
End AClient.

Module AClient' (MP : ProcessMonad) : PROCESS_FUNCTOR(MP).
  Module PE := ProcExtraction(MP).
  Module PM := MP.
  Definition proc := Eval simpl in PE.extract_proc 0 (get_proc AClient').
End AClient'.



(* code extraction from all the examples *)

Separate Extraction
         ALICE BOB CAROL (* pipeline *)
         PPSERVER PPCLIENT0 PPCLIENT1 PPCLIENT2 PPCLIENT3 PPCLIENT4 (* ping pong *)
         SELLER BUYERA BUYERB (* two buyers *)
         AServer AClient AClient'. (* calculator *)

(* leave this at the end, it needs to stay in the same directory it started *)
Cd "../../..".
