From mathcomp Require Import all_ssreflect.
From mathcomp Require Import finmap.

Require Import MPST.Actions.
Require Import MPST.AtomSets.
Require Import MPST.Global.
Require Import MPST.Local.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Notation vec := Vector.t.
Notation fin := Vectors.Fin.t.
Import Vectors.VectorDef.VectorNotations.
Definition fst_fin {n : nat} := @Vectors.Fin.F1 n.
Definition snd_fin {n : nat} := @Vectors.Fin.FS (n.+1) (fst_fin).


Open Scope mpst_scope.

Definition rlty_expand (l : rl_ty) :=
  match l with
  | rl_end => rl_end
  | rl_msg a r k => rl_msg a r k
  end.

Fixpoint rlty_expand_n (n : nat) (l : rl_ty) :=
  match l with
  | rl_end => rl_end
  | rl_msg a r k =>
    match n with
    | O => rl_msg a r k
    | S n' =>
      let fexp lbl :=
          match k lbl with
          | None => None
          | Some (T, L) => Some (T, rlty_expand_n n' L)
          end
      in
      rl_msg a r fexp
    end
  end.


Lemma rlty_unr l : l = rlty_expand l.
Proof. by case: l. Qed.

Lemma rlty_n_unr l n : l = rlty_expand_n n l.
Proof.
  move:l.
  elim n=>//=.
  case=>//.
  move=> n' Heq l0.
  (* rewrite -Heq. *)
Abort.

Inductive Proc {n : nat} (R : vec rl_ty n) : rl_ty -> Type :=
| Finish : Proc R rl_end

| Send (p : role) L
       (C : lbl /-> (mty * rl_ty)) T (l : lbl) :
  coq_ty T ->
  Proc R L ->
  C l = Some (T, L) -> (* the continuation at this label is what it has to be *)
  Proc R (rl_msg l_send p C)

| Recv (p : role)
       (C : lbl /-> (mty * rl_ty)):
    Alts R C -> Proc R (rl_msg l_recv p C)

| Jump (i : fin n) : Proc R (R [@ i])%vector
| Loop L:
    @Proc (n.+1) (L :: R)%vector (rlty_expand L) -> Proc R L
(* | Unroll L: Proc (l_rec (l_open 0 L L)) -> Proc (l_rec L) *)

(* | Unfold L : Proc (l_open 0 (l_rec L) L) -> *)
(*     Proc (l_rec L) *)

with Alts (n : nat) (R : vec rl_ty n) : (lbl /-> (mty * rl_ty)) -> Type :=
| A_sing T L l :
    (coq_ty T -> Proc R L) ->
    Alts R (extend l (T, L) (@empty rl_ty))
| A_cons T L C l :
    (coq_ty T -> Proc R L) ->
    Alts R C ->
    Alts R (extend l (T, L) C)
.

(* convenience definition for conditional processes *)
Definition IFP {n : nat} {R : vec rl_ty n} L (
             cond : bool) (p : Proc R L) (p' : Proc R L) :=
  if cond then p else p'.

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

Fixpoint gen_proc (n : nat) (R : vec rl_ty n)
         T (nm:nat) (p : Proc R T): MP.t unit
  := match p with
    | Finish => MP.pure tt
    | Send r _ _ _ l x p2 _ =>
      MP.bind (MP.send r l x) (fun _=> gen_proc nm p2)
    | Recv r C alts =>
      let base_case := fun=> MP.pure tt in
      MP.recv (@gen_alts _ _ C nm r alts base_case)

    | Loop _ p =>
      MP.loop nm (gen_proc (nm+1) p)

    (* | Unroll _ p => gen_proc nm p *)
    (* | Unfold _ p => gen_proc nm p *)

    | Jump x => MP.set_current (nm - (proj1_sig (Vectors.Fin.to_nat x)) - 1)
     end
with gen_alts (n : nat) (R : vec rl_ty n) (C : lbl /-> (mty * rl_ty))
              (nm:nat) (r : role) (alts : Alts R C)
              (f : (lbl -> MP.t unit))
     : (lbl -> MP.t unit) :=
       match alts with
       | A_sing T L l dproc =>
         let new_f (label : lbl) : MP.t unit :=
             if label == l then
               MP.bind
                 (MP.recv_one (coq_ty T) r)
                 (fun d=> gen_proc nm (dproc d))
             else
               f label
         in
         new_f
       | A_cons T _ a l dproc alts =>
         let new_f (label : lbl) : MP.t unit :=
            if label == l then
                         MP.bind
                           (MP.recv_one (coq_ty T) r)
                           (fun d=> gen_proc nm (dproc d))
                       else
                         f label
         in
         gen_alts nm r alts new_f
       end.

Definition gen_proc_ini T (nm:nat) (p : Proc ([ ]%vector) T): MP.t unit :=
  @gen_proc 0 ([ ])%vector T nm p.

(* Definition p := Eval compute in gen_proc (Fix (Rec T_nat 0)). *)
(* Extraction p. *)

(* Some examples *)

(* the finished process *)
Definition p11 := Finish ([ ]%vector). About p11.
Definition ep11 := Eval compute in gen_proc_ini 0 p11.
Extraction ep11.

Axiom C S : role. (* two roles *)

(* From mathcomp Require Import finmap. *)
(* Definition lbl_one : lbl := Lbl.fresh fset0. *)
(* we may want more "computable" labels *)

Parameter lbl_A lbl_B lbl_C : lbl.

(* receive a natural and end *)
Definition p1 := Recv C (@A_sing 0 ([ ] %vector) T_nat _ lbl_A (fun=> Finish _)).
Definition ep1 := Eval compute in gen_proc_ini 0 p1.
Extraction ep1.

(* receive one of two labels and end *)
Definition p2 := Recv C (@A_cons 0 [ ] T_nat _ _ lbl_A (fun=> Finish [ ] )
                                 (@A_sing 0 [ ] T_nat _ lbl_B (fun=> Finish [ ]))).
Definition ep2 := Eval compute in gen_proc 0 p2.
Extraction ep2.


(* recursive process that receives or stops *)
Definition p3_ty := cofix x : rl_ty := rl_msg l_recv C
                      (extend lbl_A (T_nat, rl_end)
                      (extend lbl_B (T_nat, x)
                      (empty rl_ty))).

(* Goal p3_ty = rl_msg l_recv C *)
(*               (extend lbl_A (T_nat, rl_end) *)
(*               (extend lbl_B (T_nat, p3_ty) *)
(*               (empty rl_ty))). *)
(* Proof. *)
(*   by rewrite [in LHS](rlty_unr p3_ty). *)
(* Qed. *)



Definition p3 : Proc ([ ] %vector) p3_ty :=
  Loop (Recv (R:=[p3_ty] %vector) C
    (@A_cons _ _ T_nat  _ _ lbl_A (fun=> Finish _)
    (@A_sing  _ _ T_nat  _ lbl_B (fun=> Jump  _ fst_fin)))).

Definition ep3 := Eval compute in gen_proc 0 p3.
(* Extraction ep3. *)


(* nested recursion *)

(* Definition p4_ty := *)
(*   cofix x : rl_ty := *)
(*     cofix y : rl_ty := *)
(*       rl_msg l_recv C *)
(*         (extend lbl_A (T_nat, rl_end) *)
(*         (extend lbl_B (T_nat, y) *)
(*         (extend lbl_C (T_nat, x) *)
(*         (empty rl_ty)))). *)
(* Definition p4 : Proc [ ] p4_ty := *)
(*   Loop(Loop(Recv (R := [p4_ty ; p4_ty]) C (@A_cons _ _ T_nat _ _ lbl_A (fun=> Finish _) (@A_cons _ _ T_nat _ _ lbl_B (fun=> Jump _ fst_fin) (@A_sing _ _ T_nat _ lbl_C (fun=> Jump _ snd_fin)))))). *)
(* Definition ep4 := Eval compute in gen_proc 0 p4. *)

(* An example with non-trivial nested recursion *)
Definition p4_ty :=
  cofix x : rl_ty :=
    rl_msg l_send C
           (extend lbl_A
                   (T_nat,
                    cofix y : rl_ty :=
                      rl_msg l_recv C
                             (extend lbl_A (T_nat, rl_end)
                             (extend lbl_B (T_nat, y)
                             (extend lbl_C (T_nat, x)
                             (empty rl_ty)))))
                   (empty rl_ty)).

(* unfolding X, but with an "open" type *)
Definition x_ty (x : rl_ty) :=
    rl_msg l_send C
           (extend lbl_A
                   (T_nat,
                    cofix y : rl_ty :=
                      rl_msg l_recv C
                             (extend lbl_A (T_nat, rl_end)
                             (extend lbl_B (T_nat, y)
                             (extend lbl_C (T_nat, x)
                             (empty rl_ty)))))
                   (empty rl_ty)).

(* unfolding X, with a closed type *)
Definition x_ty' : rl_ty :=
    rl_msg l_send C
           (extend lbl_A
                   (T_nat,
                    cofix y : rl_ty :=
                      rl_msg l_recv C
                             (extend lbl_A (T_nat, rl_end)
                             (extend lbl_B (T_nat, y)
                             (extend lbl_C (T_nat, p4_ty)
                             (empty rl_ty)))))
                   (empty rl_ty)).


(* unfolding Y, with an open type (with vars X and Y) *)
Definition y_ty (x y : rl_ty) :=
                      rl_msg l_recv C
                             (extend lbl_A (T_nat, rl_end)
                             (extend lbl_B (T_nat, y)
                             (extend lbl_C (T_nat, x)
                             (empty rl_ty)))).

(* An unfolding to use with the closed unfolding of Y *)

Definition y_subst := cofix y : rl_ty :=
                      rl_msg l_recv C
                             (extend lbl_A (T_nat, rl_end)
                             (extend lbl_B (T_nat, y)
                             (extend lbl_C (T_nat, p4_ty)
                             (empty rl_ty)))).
(* Unfolding Y with a closed type *)
Definition y_ty' :=
  rl_msg l_recv C
         (extend lbl_A (T_nat, rl_end)
                             (extend lbl_B (T_nat, y_subst)
                             (extend lbl_C (T_nat, p4_ty)
                             (empty rl_ty)))).

(* now definitions with the unfoldings, first with X, and then with Y *)
Definition p4_ty' := cofix x : rl_ty := x_ty'.
Definition p4_ty'' := cofix x : rl_ty :=
    rl_msg l_send C
           (extend lbl_A
                   (T_nat,
                    cofix y : rl_ty := y_ty')
                   (empty rl_ty)).

(* these equalities should hold, modulo some unfoldings *)
Goal p4_ty = p4_ty'.
rewrite/p4_ty/p4_ty'/x_ty'=>//.
Abort.

Goal p4_ty = p4_ty''.
rewrite/p4_ty/p4_ty''/y_ty'=>//.
Abort.

Lemma y_unfolding : rlty_expand y_ty' = y_subst.
by rewrite (rlty_unr y_subst).
Qed.


(* The process definition *)
Definition p4 : Proc [ ] p4_ty.
refine (Loop _).
refine (Send (R:=[p4_ty])(T:=T_nat) (l:=lbl_A) C 7 _ _).
refine (Loop _)=>//=.
refine (Recv (R:=[y_ty' ; p4_ty]) C _ ).

refine (A_cons _ _ _).
refine (fun n=> Finish _).
refine (A_cons _ _ _).
refine (fun n=> _).
rewrite (rlty_unr y_ty').
rewrite y_unfolding.
refine (Jump _ fst_fin).  (* y_ty' = y_subst <- just one unfolding away *)

refine (A_sing _ _).
refine (fun n=> _).
refine (Jump _ snd_fin).

move=>//=. (* anoying computation and equality proof, because the
              labels are postulated and they don't compute. *)
admit.
Abort.

(* old p4 *)
(* Definition p4 : Proc [ ] p4_ty := *)
(*   Loop(Loop(Recv (R := [p4_ty ; p4_ty]) C (@A_cons _ _ T_nat _ _ lbl_A (fun=> Finish _) (@A_cons _ _ T_nat _ _ lbl_B (fun=> Jump _ fst_fin) (@A_sing _ _ T_nat _ lbl_C (fun=> Jump _ snd_fin)))))). *)
(* Definition ep4 := Eval compute in gen_proc 0 p4. *)



(* Definition p4 := *)
(*   Loop(Loop(Recv C (@A_cons T_nat _ _ lbl_A (fun=> Finish) (@A_cons T_nat _ _ lbl_B (fun=> Rec 0) (@A_cons T_nat _ _ lbl_C (fun=> Rec 1) A_nil))))). *)
(* Definition ep4 := Eval compute in gen_proc 0 p4. *)
(* Extraction ep4. *)

(*
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
*)
