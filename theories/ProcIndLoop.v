From mathcomp Require Import all_ssreflect.
From mathcomp Require Import finmap.


Require Import MPST.Actions.
Require Import MPST.AtomSets.
Require Import MPST.Global.
Require Import MPST.Local.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Inductive Proc : l_ty -> Type :=
| Finish : Proc l_end
| Recv a (p : role) :
    Alts a -> Proc (l_msg l_recv p a)

| Rec : forall (v : nat), Proc (l_var v)
| Loop L: Proc L -> Proc (l_rec L)
| Unroll L: Proc (l_rec (l_open 0 L L)) -> Proc (l_rec L)

| Unfold L : Proc (l_open 0 (l_rec L) L) ->
    Proc (l_rec L)

| Send (p : role) L a T (l : lbl) :
  coq_ty T ->
  Proc L ->
  (l, (T, L)) \in a ->
  Proc (l_msg l_send p a)
(* | Case T Ts L : coq_ty T ->
           CAlts Ts L ->
           Proc L
 *)

with Alts : seq (lbl * (mty * l_ty)) -> Type :=
| A_nil : Alts [::]
| A_cons T L a l : (coq_ty T -> Proc L) ->
                   Alts a ->
                   Alts ((l, (T, L)) :: a)
(*
with CAlts : seq mty -> l_ty -> Type :=
| C_sing T L : (coq_ty T -> Proc L) -> CAlts [:: T] L
| C_cons T L Ts : (coq_ty T -> Proc L) ->
                 CAlts Ts L ->
                 CAlts (T :: Ts) L
*)
.

(* convenience definition for conditional processes *)
Definition IFP L (n : bool) (p : Proc L) (p' : Proc L) :=
  if n then p else p'.

(* Fixpoint proc_lty :
 *)

From Coq Require Extraction.
Module MP.
  Parameter t : Type -> Type.

  Parameter send : forall T, role -> lbl -> T -> t unit.
  (* Extract Constant send => "ocaml_send". *)

  Parameter recv : (lbl -> t unit) -> t unit.
  Parameter recv_one : forall T, role -> t T.

  Parameter bind : forall T1 T2, t T1 -> (T1 -> t T2) -> t T2.

  Parameter pure : forall T1, T1 -> t T1.

  Parameter loop : forall T1, nat -> t T1 -> t T1.
  Parameter set_current: nat -> t unit.

  Parameter rec : forall T1, nat -> t T1.
End MP.

Fixpoint gen_proc T (n:nat) (p : Proc T): MP.t unit
  := match p with
    | Finish => MP.pure tt
    | Send r _ _ _ l x p2 _ =>
      MP.bind (MP.send r l x) (fun _=> gen_proc n p2)
    | Recv a r alts =>
      let base_case := fun=> MP.pure tt in
      MP.recv (@gen_alts a n r alts base_case)

    | Loop _ p =>
      MP.loop n (gen_proc (n+1) p)

    | Unroll _ p => gen_proc n p

    | Unfold _ p => gen_proc n p

    | Rec x => MP.set_current (n - x - 1)
     end
with gen_alts (a :seq (lbl * (mty * l_ty)))
              (n:nat) (r : role) (alts : Alts a)
              (f : (lbl -> MP.t unit))
     : (lbl -> MP.t unit) :=
       match alts with
       | A_nil => f
       | A_cons T _ a l dproc alts =>
         let new_f (label : lbl) : MP.t unit :=
            if label == l then
                         MP.bind
                           (MP.recv_one (coq_ty T) r)
                           (fun d=> gen_proc n (dproc d))
                       else
                         f label
         in
         gen_alts n r alts new_f
       end.

(* Definition p := Eval compute in gen_proc (Fix (Rec T_nat 0)). *)
(* Extraction p. *)

(* Some examples *)

(* the finished process *)
Definition p11 := Finish.
Definition ep11 := Eval compute in gen_proc 0 p11.
(* Extraction ep11. *)

Axiom C S : role. (* two roles *)

(* From mathcomp Require Import finmap. *)
(* Definition lbl_one : lbl := Lbl.fresh fset0. *)
(* we may want more "computable" labels *)

Parameter lbl_A lbl_B lbl_C : lbl.

(* receive a natural and end *)
Definition p1 := Recv C (@A_cons T_nat _ _ lbl_A (fun=> Finish) A_nil).
Definition ep1 := Eval compute in gen_proc 0 p1.
(* Extraction ep1. *)

(* receive one of two labels and end *)
Definition p2 := Recv C (@A_cons T_nat _ _ lbl_A (fun=> Finish)
                                 (@A_cons T_nat _ _ lbl_B (fun=> Finish) A_nil)).
Definition ep2 := Eval compute in gen_proc 0 p2.
(* Extraction ep2. *)

(* recursive process that receives or stops *)
Definition p3 :=
  Loop(Recv C (@A_cons T_nat _ _ lbl_A (fun=> Finish) (@A_cons T_nat _ _ lbl_B (fun=> Rec 0) A_nil))).
Definition ep3 := Eval compute in gen_proc 0 p3.
(* Extraction ep3. *)

(* nested recursion *)
Definition p4 :=
  Loop(Loop(Recv C (@A_cons T_nat _ _ lbl_A (fun=> Finish) (@A_cons T_nat _ _ lbl_B (fun=> Rec 0) (@A_cons T_nat _ _ lbl_C (fun=> Rec 1) A_nil))))).
Definition ep4 := Eval compute in gen_proc 0 p4.
(* Extraction ep4. *)

(* Ping pong example *)

Parameter Ping Pong Bye : lbl.  (* the needed labels *)

Definition PP_C : l_ty :=
  l_rec
    (l_msg l_send S
           [:: (Bye, (T_unit, l_end))
            ; (Ping, (T_nat, l_msg l_recv S
                                   [:: (Pong, (T_nat, l_var 0))]))]).

Definition PP_S : l_ty :=
  l_rec
    (l_msg l_recv C
           [:: (Bye, (T_unit, l_end))
            ; (Ping, (T_nat, l_msg l_send C
                                   [:: (Pong, (T_nat, l_var 0))]))]).

(* server: answers the pings with the same data *)
Definition PingPongServer : Proc PP_S.
  refine (Loop (@Recv _ C _)).
  (*alts*)
  refine (@A_cons T_unit _ _ Bye (fun=> Finish)
                  (@A_cons T_nat _ _ Ping (fun d=> _) A_nil)).
  refine (@Send C _ _ T_nat Pong d (Rec 0) _).
  apply mem_head.
Defined.

(* sends ping, waits for pong, repeat for ever *)
Definition PingPongClient1 : Proc PP_C.
  refine (Loop (@Send S _ _ T_nat Ping 7 (@Recv _ S _) _)).
  (* alts *)
  refine (@A_cons T_nat _ _ Pong (fun=> Rec 0) A_nil).
  (* proof that we used the labels under the right type *)
  apply (@mem_drop 1)=>//=.
  apply mem_head.
Defined.

(* sends ping, waits for pong, sends bye *)
Definition PingPongClient2 : Proc PP_C.
  refine (Loop (@Send S _ _ T_nat Ping 7 (@Recv _ S _) _)).
  (* alts *)
  refine (@A_cons T_nat _ _ Pong (fun=> _) A_nil).

  refine (@Send S _ _ T_unit Bye tt Finish _).
  apply mem_head.

  apply (@mem_drop 1)=>//=.
  (* ?? <- fails because it should have unrolled the protocol *)
Abort.

Definition PingPongClient2 : Proc PP_C.
  refine (Unroll _)=>/=.        (* now it unrolls once before starting *)
  refine (Loop (@Send S _ _ T_nat Ping 3 (@Recv _ S _) _)).
  (* alts *)
  refine (@A_cons T_nat _ _ Pong (fun=> _) A_nil)=>//=.

  refine (@Send S _ _ T_unit Bye tt Finish _).
  apply mem_head.

  apply (@mem_drop 1)=>//=.
  apply: mem_head.
Defined.
Definition ppc2 := Eval compute in gen_proc 0 PingPongClient2.
(* Extraction ppc2. *)

(* sends ping, waits for pong, repeats while payload is not 3 *)
Definition PingPongClient3 : Proc PP_C.
  refine (Unroll _)=>/=.
  refine (Loop (@Send S _ _ T_nat Ping 3 (@Recv _ S _) _)).
  (* alts *)
  refine (@A_cons T_nat _ _ Pong (fun n=> _) A_nil)=>//=.

  (* finish if you got 3 *)
  refine (IFP (n == 3) (@Send S _ _ T_unit Bye tt Finish _) _).

  apply mem_head.

  refine (@Send S _ _ T_nat Ping 7 (@Recv _ S _) _).
  refine (@A_cons T_nat _ _ Pong (fun=> _) A_nil).
  refine (Rec 0).

  apply (@mem_drop 1)=>/=.
  rewrite drop0.
  apply mem_head.

  apply (@mem_drop 1)=>//=.
  apply mem_head.
Defined.
Definition ppc3 := Eval compute in gen_proc 0 PingPongClient3.
(* Extraction ppc3. *)

(* Section Semantics. *)

(*   SearchAbout rl_ty. *)

(*   Notation penv := {fmap role -> {T: _ & Proc T}}. *)
(*   Notation pqenv := {fmap role * role -> seq (lbl * {T: mty & coq_ty T}) }. *)

(*   Inductive pstep : act -> penv * pqenv -> penv * pqenv -> Prop := *)
(*   (* TBD *) *)
(*   . *)

(*   Lemma process_behave *)
(*         (a : act) *)
(*         (P  P' : {fmap role -> rl_ty}) *)
(*         (Q Q' : {fmap role * role -> seq (lbl * mty)}) *)
(*         (rP rP' : {fmap role -> {T : l_ty & Proc T}}) *)
(*         (rQ rQ' : {fmap role * role -> seq (lbl * {T : mty & coq_ty T})}) *)
(*     : *)
(*        pstep a (rP, rQ) (rP', rQ') -> lstep a (P, Q) (P', Q'). *)
(* Abort. *)

(* End Semantics. *)
