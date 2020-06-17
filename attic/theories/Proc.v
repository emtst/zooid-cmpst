From mathcomp Require Import all_ssreflect seq.
From mathcomp Require Import finmap.

Require Import MPST.Actions.
Require Import MPST.AtomSets.
Require Import MPST.Global.
Require Import MPST.Local.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Fixpoint unfold l :=
  match l with
    | l_end => l_end
    | l_var v => l_var v
    | l_msg a r Ks =>
      l_msg a r
            (map
               (fun en =>
                  let:
                       (lbl, (pl, l)) := en
                  in
                  (lbl, (pl,  unfold l)))
               Ks)
    | l_rec l => l_open 0 (l_rec l) (unfold l)
  end.




Inductive Proc : l_ty -> Type :=
| Finish : Proc l_end

| Jump : forall (v : nat), Proc (l_var v)
| Loop L: Proc L -> Proc (l_rec L)

| Recv a (p : role) : Alts a -> Proc (l_msg l_recv p a)
| Send (p : role) L a T (l : lbl) :
  coq_ty T ->
  Proc L ->
  (l, (T, L)) \in a ->
  Proc (l_msg l_send p a)

with Alts : seq (lbl * (mty * l_ty)) -> Type :=
| A_sing T L l : (coq_ty T -> Proc L) -> Alts [:: (l, (T, L))]
| A_cons T L a l : (coq_ty T -> Proc L) ->
                   Alts a ->
                   Alts ((l, (T, L)) :: a)
.

(* Unset Printing Notations. *)

Fixpoint lookup_alt_cont T (a : seq (lbl * (mty * l_ty)))
          (* the existential is silly, it should be what a says *)
          (l : lbl) (alts : Alts a): option (sigT (fun x => (coq_ty T -> Proc x))) :=
  match alts with
  (* | A_sing _ _ l' dproc => *)
  (*   if l == l' then Some dproc else None *)
  |_ => None
  end.

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
End MP.



(* Module MP'. *)
(*   Parameter t : l_ty -> Type. *)

(*   (* Parameter bind : forall T1 T2, t T1 -> (T1 -> t T2) -> t T2. *) *)
(*   Parameter pure : t l_end. *)

(*   Parameter send : forall (p : role) L a T (l : lbl), *)
(*       coq_ty T -> (l, (T, L)) \in a -> *)
(*       t (l_msg l_send p a). *)
(*   (* Extract Constant send => "ocaml_send". *) *)

(*   Print l_lts_. *)

(*   (* Parameter recv : (lbl -> t unit) -> t unit. *) *)
(*   (* Parameter recv_one : forall T, role -> t T. *) *)


(*   (* Parameter loop : forall T1, nat -> t T1 -> t T1. *) *)
(*   (* Parameter set_current: nat -> t unit. *) *)

(*   (* Parameter rec : forall T1, nat -> t T1. *) *)
(* End MP'. *)

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

    | Jump x => MP.set_current (n - x - 1)
     end
with gen_alts (a :seq (lbl * (mty * l_ty)))
              (n:nat) (r : role) (alts : Alts a)
              (f : (lbl -> MP.t unit))
     : (lbl -> MP.t unit) :=
       let new_f L T (dproc : coq_ty T -> Proc L) l (label : lbl) : MP.t unit :=
           if label == l then
             MP.bind
               (MP.recv_one (coq_ty T) r)
               (fun d=> gen_proc n (dproc d))
           else
             f label
       in
       match alts with
       | A_sing T _ l dproc =>
         new_f _ T dproc l
       | A_cons T _ a l dproc alts =>
         gen_alts n r alts (new_f _ T dproc l)
       end.

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
Definition p1 := Recv C (@A_sing T_nat  _ lbl_A (fun=> Finish)).
Definition ep1 := Eval compute in gen_proc 0 p1.
(* Extraction ep1. *)

(* receive one of two labels and end *)
Definition p2 := Recv C (@A_cons T_nat _ _ lbl_A (fun=> Finish)
                                 (@A_sing T_nat _ lbl_B (fun=> Finish))).
Definition ep2 := Eval compute in gen_proc 0 p2.
(* Extraction ep2. *)

(* recursive process that receives or stops *)
Definition p3 :=
  Loop(Recv C (@A_cons T_nat _ _ lbl_A (fun=> Finish) (@A_sing T_nat  _ lbl_B (fun=> Jump 0)))).
Definition ep3 := Eval compute in gen_proc 0 p3.
(* Extraction ep3. *)

(* nested recursion *)
Definition p4 :=
  Loop(Loop(Recv C (@A_cons T_nat _ _ lbl_A (fun=> Finish) (@A_cons T_nat _ _ lbl_B (fun=> Jump 0) (@A_sing T_nat _ lbl_C (fun=> Jump 1)))))).
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
                  (@A_sing T_nat  _ Ping (fun d=> _))).
  refine (@Send C _ _ T_nat Pong d (Jump 0) _).
  apply mem_head.
Defined.

(* the client that always says bye *)
Definition PingPongClientBye : Proc PP_C.
  refine (Loop (@Send S _ _ T_unit Bye tt Finish _)).
  apply mem_head.
Qed.

(* sends ping, waits for pong, repeat for ever *)
Definition PingPongClient1 : Proc PP_C.
  refine (Loop (@Send S _ _ T_nat Ping 7 (@Recv _ S _) _)).
  (* alts *)
  refine (@A_sing T_nat  _ Pong (fun=> Jump 0)).
  (* proof that we used the labels under the right type *)
  apply (@mem_drop 1)=>//=.
  apply mem_head.
Defined.

(* sends ping, waits for pong, sends bye *)
Definition PingPongClient2 : Proc PP_C.
  refine (Loop (@Send S _ _ T_nat Ping 7 (@Recv _ S _) _)).
  (* alts *)
  refine (@A_sing T_nat _ Pong (fun=> _)).

  refine (@Send S _ _ T_unit Bye tt Finish _).
  apply mem_head.

  apply (@mem_drop 1)=>//=.
  (* ?? <- fails because it should have unrolled the protocol *)
Abort.

Definition PP_C_unrolled := Eval compute in unfold PP_C.
(* Print PP_C_unrolled. *)

Definition PingPongClient2 : Proc PP_C_unrolled.
  rewrite/PP_C_unrolled. (* not necessary, just for convenience *)
  refine (@Send S _ _ T_nat Ping 3 (@Recv _ S _) _).
  (* alts *)
  refine (@A_sing T_nat _ Pong (fun=> _))=>//=.
  refine PingPongClientBye.

  apply (@mem_drop 1)=>//=.
  apply mem_head.
Defined.

Definition ppc2 := Eval compute in gen_proc 0 PingPongClient2.
(* Extraction ppc2. *)

(* sends ping, waits for pong, repeats while payload is not 3 *)
Definition PingPongClient3 : Proc PP_C_unrolled.
  refine (@Send S _ _ T_nat Ping 3 (@Recv _ S _) _).
  (* alts *)
  refine (@A_sing T_nat _ Pong (fun n=> _))=>//=.
  refine (Loop _).
  (* finish if you got 3 *)
  refine (IFP (n == 3) (@Send S _ _ T_unit Bye tt Finish _) _).

  apply mem_head.

  refine (@Send S _ _ T_nat Ping 7 (@Recv _ S _) _).
  refine (@A_sing T_nat _ Pong (fun=> _)).
  refine (Jump 0).

  apply (@mem_drop 1)=>/=.
  rewrite drop0.
  apply mem_head.

  apply (@mem_drop 1)=>//=.
  apply mem_head.
Defined.

Definition ppc3 := Eval compute in gen_proc 0 PingPongClient3.
(* Extraction ppc3. *)

Section OperationalSemantics.

  (* runtime action *)
  Inductive rt_act :=
  | mk_rt_act (a : l_act) (p : role) (q : role) (l : lbl) (T : mty) (t :  coq_ty T).

  Definition erase_act a :=
  let: mk_rt_act a p q l T _ := a in mk_act a p q l T.



(*   SearchAbout rl_ty. *)

  Notation penv := {fmap role -> {T: l_ty & Proc T}}.

  (* Definition eq_penv (P P' : penv) := *)
  (*   match P, P' with *)
  (*   |  _, _ => false *)
  (*   end. *)

  (* Lemma penv_eqP : Equality.axiom eq_penv. *)
  (* (* Proof. by rewrite /Equality.axiom => [[] []/=]; constructor. Qed. *) *)
  (* Admitted. *)

  (* Definition penv_eqMixin := EqMixin penv_eqP. *)
  (* Canonical penv_eqType := Eval hnf in EqType penv penv_eqMixin. *)

  (* Definition pqenv := {fmap role * role -> seq (lbl * {T: mty & coq_ty T}) }. *)

  (* Definition eq_pqenv (Q Q' : pqenv) := *)
  (*   match Q, Q' with *)
  (*   |  _, _ => false *)
  (*   end. *)

  (* Lemma pqenv_eqP : Equality.axiom eq_pqenv. *)
  (* (* Proof. by rewrite /Equality.axiom => [[] []/=]; constructor. Qed. *) *)
  (* Admitted. *)

  (* Definition pqenv_eqMixin := EqMixin pqenv_eqP. *)
  (* Canonical pqenv_eqType := Eval hnf in EqType pqenv pqenv_eqMixin. *)

  (* Definition penq (qs : pqenv) k v := *)
  (*   match qs.[? k] with *)
  (*   | Some vs => qs.[ k <- app vs [:: v] ] *)
  (*   | None => qs.[ k <- [:: v]] *)
  (*   end%fmap. *)

  (* Definition pdeq (qs : pqenv) k := *)
  (*   match qs.[? k] with *)
  (*   | Some vs => *)
  (*     match vs with *)
  (*     | [:: v] => Some (v, qs.[~ k]) *)
  (*     | v :: vs => Some (v, qs.[k <- vs]) *)
  (*       (* if vs == [::] then Some (v, qs.[~ k]) *) *)
  (*       (* else Some (v, qs.[k <- vs]) *) *)
  (*     | [::] => None *)
  (*     end *)
  (*   | None => None *)
  (*   end%fmap. *)

  Definition process_admits_act
             T (P : Proc T) (a : l_act) (p q : role) (l : lbl) (t : mty) :
    option l_ty.
  Abort.

  (* Inductive pstep : act -> penv * pqenv -> penv * pqenv -> Prop := *)
  (* | ls_send (T : mty) (t : coq_ty T) p q lb (P P' : penv) (Q Q' : pqenv) : *)
  (*     Q' == penq Q (p, q) (lb, (existT _ T t)) -> *)
  (*     (* do_act P l_send p q lb t = Some P' -> *) *)
  (*     pstep (a_send p q lb T) (P, Q) (P', Q') *) (* a_send ceased to exist *)
  (* | ls_recv t p q lb (P P' : penv) (Q Q' : pqenv) : *)
  (*     (* deq Q (p, q) == Some ((lb, t), Q') -> *) *)
  (*     (* do_act P l_recv q p lb t = Some P' -> *) *)
  (*     pstep (a_recv p q lb t) (P, Q) (P', Q') *)
  (* . *)


  Definition look_proc (E : penv) p :=
    match E.[? p] with
    | Some L => L
    | None => existT _ l_end Finish
    end%fmap.

  Section OneProc.


    Definition run_rt_act L (P : Proc L) (A : rt_act) : (Proc (run_act_l_ty L (erase_act A))).
      refine (let: (mk_rt_act a p q l T t) := A in _)=>//=.

      (* case P; try by rewrite/run_act_l_ty/do_act_l_ty. *)
      (* constructor. *)
      (* constructor. *)

      (* rewrite/run_act_l_ty=>//=. *)
      (* admit. *)

      (* admit. *)

      move: P l.
      case L ; try by rewrite/run_act_l_ty/do_act_l_ty.

      case. (* casing on the act *)

      (* send action *)
      rewrite/run_act_l_ty/do_act_l_ty.
      case a=>//=.
      move=>r ; case (q == r)=>//=.

      {
        move=> Ks P l.
        destruct (lookup_l_ty_cont Ks l) eqn: Lu.
        destruct p0.

        case (T == m).


        (* inversion P => l' Lu'. *)




        admit. (* ? *)

        easy.

        (* move=> Ks P l ; case (lookup_l_ty_cont Ks l)=>//=. (* forgets the lookup is in Ks *) *)
        (* case. *)
        (* move=> a0; case (T == a0). *)

        (* admit. *)

        (* by []. *)
        easy.
      }

      (* other cases where the process does not step *)
      by move=>Ks P l ; case (lookup_l_ty_cont Ks l)=>//= ; case.
      by move=>r Ks P l ; case (lookup_l_ty_cont Ks l)=>//= ; case.

      (* receive case *)

    Abort.

  End OneProc.

  Definition do_rt_act (P : penv) (A : rt_act) : option penv :=
    let: (mk_rt_act a p q l t data) := A in
    match a, look_proc P p with
    | l_send, existT  _ (Send q' L _ t' l' T' P' _) =>
      if (q == q') && (l == l') && (t == t') then (* && (T == T') then *) (* <- we may need to say this *)
        Some P.[p <- existT _ L P']
      else None
    | l_recv, existT _ (Recv _ q' alts) =>
      if q == q' then
        match lookup_alt_cont t l alts with
          | Some (existT L f) => Some P.[p <- (existT _ L (f data))]
          | None => None
        end
      else None
    | _, _ => None
    end%fmap.

  Definition run_rt_step (P : penv) (A : rt_act) : penv :=
    match do_rt_act P A with
    | Some P => P
    | None => P
    end.

  Inductive pstep : rt_act -> penv -> penv -> Prop :=
  | ls_rel (Ti : mty) (t : coq_ty Ti)  (sact :rt_act) (P P' : penv) :
      pstep sact P (run_rt_step P sact)
  .

 Definition related (rP : penv) (P : {fmap role -> rl_ty}) : Prop :=
   forall p, LUnroll (projT1 (look_proc rP p)) (look P p).

  Lemma process_behave
        (a : rt_act)
        (PQ  PQ' : {fmap role -> rl_ty} * {fmap role * role -> seq (lbl * mty)})
        (rP rP' : penv)
    :
      related rP PQ.1 ->
      rP' = run_rt_step rP a ->
      PQ' = run_step (erase_act a) PQ ->

      pstep a rP rP' -> lstep (erase_act a) PQ PQ'.
Abort.

End OperationalSemantics.