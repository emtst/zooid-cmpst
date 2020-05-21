From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

From Paco Require Import paco paco2.

Require Import MPST.Atom.
Require Import MPST.AtomSets.
Require Import MPST.Forall.
Require Import MPST.LNVar.
Require Import MPST.Global.
Require Import MPST.Local.
Require Import MPST.Actions.
Require Import MPST.Projection.
Require Import MPST.WellFormed.


Section QProjection.

(*next Variable and Definition may be useless*)
Variable PAR : {fset role}.

Definition PAR2 := (PAR `*` PAR)%fset.

Open Scope fmap.

  Definition qproj_rel := ig_ty -> {fmap role * role -> seq (lbl * mty) } -> Prop.
  Inductive qProject : qproj_rel :=
  | qprj_end G : qProject (ig_end G) [fmap]%fmap(*[fmap qq:PAR2 => [::]]*)
  | qprj_none p p' CONT Q :
      (forall l Ty G, CONT l = Some (Ty, G) -> qProject G Q) ->
      Q.[? (p,p')] = None ->
      qProject (ig_msg None p p' CONT) Q
  | qprj_some p p' CONT l Ty G Q Q':
      CONT l = Some (Ty, G) ->
      deq Q' (p, p') == Some ((l, Ty), Q) ->
      qProject G Q ->
      qProject (ig_msg (Some l) p p' CONT) Q'
  .
  Hint Constructors qProject.



(*L to D and F; about the next 6 lemmas:
  - should be moved
  - might be be turned into 2 or even 0
*)

  Lemma qProject_end_inv_aux Q iG G:
    qProject iG Q ->  iG = (ig_end G) ->
    Q = ([fmap]%fmap).
  Proof.
  case =>//=.
  Qed.

  Lemma qProject_end_inv Q G:
  qProject (ig_end G) Q ->
    Q = ([fmap]%fmap).
  Proof.
  by move=> hp; apply: (@qProject_end_inv_aux Q _ G hp).
  Qed.


  Lemma qProject_None_inv_aux F T C l Ty G Q GG:
    qProject GG Q ->
    GG = (ig_msg None F T C) ->
    Q.[? (F,T)] = None /\
    (C l = Some (Ty, G) -> qProject G Q).
  Proof.
  case =>//=.
  move=> p p' CONT Q0 IH neq [eq1 eq2 eq3].
  split; [by rewrite -eq1 -eq2| rewrite -eq3].
  by apply IH.
  Qed.

  Lemma qProject_None_inv F T C l Ty G Q (*Q'*):
    qProject (ig_msg None F T C) Q ->
    Q.[? (F,T)] = None /\
    (C l = Some (Ty, G) -> qProject G Q).
  Proof.
  move=> hp; move: (@ qProject_None_inv_aux F T C l Ty G _ _ hp).
  by move=> triv; apply triv.
  Qed.


  Lemma qProject_Some_inv_aux l F T C Q GG:
    qProject GG Q ->
    GG = (ig_msg (Some l) F T C) ->
    (exists Ty G Q',
    C l = Some (Ty, G) /\
    deq Q (F, T) == Some ((l, Ty), Q') /\
    qProject G Q').
  Proof.
  case =>//.
  move=> p p' CONT l0 Ty G Q0 Q' CONTL0 deqQ' qpro [eq1 eq2 eq3 eq4].
  rewrite -eq1 -eq2 -eq3 -eq4;  exists Ty, G, Q0.
  by split; [| split; [|]].
  Qed.

  Lemma qProject_Some_inv l F T C Q:
    qProject (ig_msg (Some l) F T C) Q ->
    exists Ty G Q', C l = Some (Ty, G) /\
    deq Q (F, T) == Some ((l, Ty), Q') /\
    qProject G Q'.
  Proof.
  move=> hp; move: (@qProject_Some_inv_aux l F T C Q _ hp).
  by move=> triv; apply triv.
  Qed.

(*next lemma to be renamed and moved*)
  Lemma deq_elsewhere Q Q' k0 k L Ty:
    deq Q' k0 == Some (L, Ty, Q) -> k != k0 ->
  Q'.[?k]=Q.[?k].
  Proof.
  rewrite /deq; case E: (Q'.[? k0]) =>[qs|] //=; case qs => [|q qs0] //=.
  case: ifP; move=> _; rewrite -(rwP eqP); move=> [_ <-].
  + by rewrite fnd_rem1; case: ifP.
  + by rewrite fnd_set; case: ifP.
  Qed.


  (* Lemma qProject_rcv_Free_None p q G Q: *)
  (* qProject G Q -> ig_wfcont G -> rcv_Free p q G -> *)
  (* Q.[?(p,q)] = None. *)
  (* Proof. *)
  (* elim. *)
  (* + by move=> G0 wfc triv; apply fnd_fmap0. *)
  (* + move=> F T C {}Q neq qpro_all ih wfc. *)
  (*   move: (ig_wfcont_msg_inv wfc). *)
  (*   elim=> _; elim; elim=> L; elim=> Ty; elim=> G0. *)
  (*   elim=> CL wfc0 wfcall. *)
  (*   elim/rcvFree_inv =>//=. *)
  (*   - move=> rfree p' q' C' rfree0 eqp eqq [eq1 eq2 eq3]. *)
  (*     apply: (ih _ _ _ CL wfc0); rewrite eq3 in rfree0. *)
  (*     by apply: (rfree0 _ _ _ CL). *)
  (*   - move=> rfree p0 p' q0 q' o C' rfree0 or eqp eqq [eq1 eq2 eq3 eq4]. *)
  (*     apply: (ih _ _ _ CL wfc0); rewrite eq4 in rfree0. *)
  (*     by apply: (rfree0 _ _ _ CL). *)
  (* + move=> F T C L Ty G0 {}Q Q' neq CL deqQ' qpro ih wfc. *)
  (*   move: (ig_wfcont_msg_inv wfc). *)
  (*   elim=> _; elim=> _ wfcall. *)
  (*   elim/rcvFree_inv =>//=. *)
  (*   move=> rfree p0 p' q0 q' o C' rfree0 or eqp eqq [eq1 eq2 eq3 eq4]. *)
  (*   rewrite (deq_elsewhere deqQ'); [|]. *)
  (*   - by rewrite eq4 in rfree0; apply (ih (wfcall _ _ _ CL) (rfree0 _ _ _ CL)). *)
  (*   - by rewrite -eq2 -eq3 xpair_eqE negb_and. *)
  (* Qed. *)


(*maybe to be moved*)

  Lemma deq_singleton (Q:{fmap role * role -> seq (lbl * mty) }) p q v:
    Q.[?(p,q)] == None ->
    deq Q.[(p, q) <- [:: v]] (p, q) = Some (v, Q).
  Proof.
  move=> Qnone; rewrite /deq fnd_set; case: ifP; rewrite eq_refl //=; elim.
  apply: f_equal; apply: injective_projections =>//=.
  rewrite -fmapP; move=> pq; rewrite fnd_rem1; case: ifP.
  + move=> neq; rewrite fnd_set; case: ifP =>//=.
    by rewrite (negbTE neq) //=.
  + move=> eq; move: (negbNE (negbT eq)).
    by rewrite -(rwP eqP) =>->; rewrite (rwP eqP) eq_sym.
  Qed.


(*
  Definition deq_rinv
    p p' l Ty (Q: {fmap role * role -> seq (lbl * mty) }):=
  match Q.[? (p,p')] with
    | None => Q.[(p,p') <- ([::(l,Ty)])]
    | Some q => Q.[(p,p') <- ( cons (l,Ty) q ) ]
  end%fmap.


 Lemma deq_rinv_deq p p' l Ty
    (Q: {fmap role * role -> seq (lbl * mty) }):
    (*Q.[? (p,p')] != Some [::]*)
    (forall q q', Q.[?(q,q')] != Some [::])->
    deq (deq_rinv p p' l Ty Q) (p, p') = Some ((l, Ty), Q).
  Proof.
  move=> hp; rewrite /deq_rinv.
  case E: Q.[? (p,p')] => [qs|]; rewrite /deq.
  + rewrite fnd_set; case: ifP =>//=; [|by rewrite eq_refl].
    have noneq: qs != [::]. by move: (hp p p'); rewrite E.
    move=> _; case: ifP.
    * by rewrite -(rwP eqP); move=> eq; rewrite eq in noneq.
    * move=> _; rewrite setfC; case: ifP =>//=; [|by rewrite eq_refl].
      move=> _; apply f_equal; rewrite pair_equal_spec; split=>//=.
      rewrite -fmapP; move=> k; rewrite fnd_set; case: ifP =>//=.
      by rewrite -(rwP eqP); move=>->.
  + rewrite fnd_set; case: ifP =>//=; [|by rewrite eq_refl].
    move=> _; apply f_equal; rewrite pair_equal_spec; split=>//=.
    rewrite -fmapP; move=> k; rewrite remf1_set.
    case: ifP; [move=> _; rewrite fnd_rem1|by rewrite eq_refl].
    case: ifP; [by []|rewrite (rwP negPf) -(rwP negPn) -(rwP eqP)].
    by move=>->.
  Qed.

  Lemma rcv_Free_None_inv_aux GG FROM TO CONT p q l Ty G:
    GG = (rg_msg None FROM TO CONT) -> rcv_Free (p,q) GG ->
    CONT l = Some (Ty, G) ->
    rcv_Free (p,q) G.
  Proof.
  move=> eq hp; punfold hp; [|by apply rFree_monotone].
  move: hp eq  => [ | | ] =>//[].
  + move=> {}p {}q C hp [peq qeq CONTeq] CONTl.
    rewrite -CONTeq in CONTl; move: (hp _ _ _ CONTl).
    by rewrite /upaco2 /rcv_Free /bot2; elim.
  + move=> {}p p' {}q q' o C hp neq [opteq peq qeq CONTeq] CONTl.
    rewrite -CONTeq in CONTl; move: (hp _ _ _ CONTl).
    by rewrite /upaco2 /rcv_Free /bot2; elim.
  Qed.

  Lemma rcv_Free_None_inv FROM TO CONT p q l Ty G:
    rcv_Free (p,q) (rg_msg None FROM TO CONT) ->
    CONT l = Some (Ty, G) ->
    rcv_Free (p,q) G.
  Proof.
  by apply: rcv_Free_None_inv_aux.
  Qed.

  Lemma rcv_Free_Some_inv_aux GG FROM TO L CONT p q :
    GG = (rg_msg (Some L) FROM TO CONT) -> rcv_Free (p,q) GG ->
    (p,q) != (FROM, TO) /\
    (forall l Ty G, CONT l = Some (Ty, G) -> rcv_Free (p,q) G).
  Proof.
  move=> eq hp; punfold hp; [|by apply rFree_monotone].
  move: hp eq  => [ | | ] =>//[].
  move=> {}p p' {}q q' o C hp neq [opteq peq qeq CONTeq].
  split; [by rewrite peq qeq in neq| move=> l Ty G CONTl].
  rewrite -CONTeq in CONTl; move: (hp _ _ _ CONTl).
  by rewrite /upaco2 /rcv_Free /bot2; elim.
  Qed.

  Lemma rcv_Free_Some_inv FROM TO CONT p q L:
    rcv_Free (p,q) (rg_msg (Some L) FROM TO CONT) ->
    (p,q) != (FROM, TO) /\
    (forall l Ty G, CONT l = Some (Ty, G) -> rcv_Free (p,q) G).
  Proof.
  by apply: rcv_Free_Some_inv_aux.
  Qed.

  Lemma deq_eq_where_notempty Q Q0 p q FROM TO L Ty Qc :
    Q = Q0.[~(p,q)] -> (p, q) != (FROM, TO) ->
    deq Q0 (FROM, TO) == Some (L, Ty, Qc) ->
    deq Q (FROM, TO) == Some (L, Ty, Qc.[~(p,q)]).
  Proof.
  move=> Qeq neqpq. rewrite /deq.
  have QFTeq: Q0.[? (FROM, TO)] = Q.[? (FROM, TO)].
    rewrite Qeq fnd_rem1; rewrite eq_sym in neqpq.
    by move: neqpq; case: ifP =>//.
  rewrite QFTeq; case eqm1: Q.[? (FROM, TO)] => [qs|] //=.
  case eqm2: qs  => [|q0 qs0] //=; case: ifP.
  + move=> _; rewrite -(rwP eqP); move=> [eqq0 eqQc].
    rewrite -(rwP eqP); apply f_equal, injective_projections =>//=.
    by rewrite -eqQc Qeq remf_comp remf_comp fsetUC //=.
  + move=> _; rewrite -(rwP eqP); move=> [eqq0 eqQc].
    rewrite -(rwP eqP); apply f_equal, injective_projections =>//=.
    by rewrite -eqQc Qeq remf1_set; move: neqpq; case: ifP =>//=.
  Qed.

  Lemma rcv_Free_qProject p q G Q0 Q:
    rcv_Free (p,q) G -> qProject G Q0 ->
    g_wfcont G -> Q = Q0.[~ (p,q)]
    -> qProject G Q.
  Proof.
  move=> hp1 hp2 hp3 hp4.
  move: (conj hp1 (conj hp2 (conj hp3 hp4))) => {hp1 hp2 hp3 hp4}.
  move=> /(ex_intro (fun Q=> _) Q0) {Q0};  move: G Q.
  apply /paco2_acc; move=> r0 _ CIH G Q; elim=> Q0.
  elim=> rfree; elim=> qpro; elim=> wfco Qeq.
  move: wfco rfree qpro; case: G.
  + move=> wfco rfree qpro; move: (qProject_end_inv qpro) Qeq=>->=>->.
    by rewrite remf1_id //=; apply /paco2_fold; apply qprj_end.
  + move=> o FROM TO CONT wfco rfree qpro; apply /paco2_fold.
    move: wfco rfree qpro; case: o.
    * move=> L wfco rfree qpro; move: (rcv_Free_Some_inv rfree).
      elim=> neqpq contfree; move: (qProject_Some_inv qpro).
      elim=> neq; elim=> Ty; elim=> G; elim=> Qc.
      elim=> CONTL; elim=> deqeq qproc.
      apply: (@qprj_some _ _ _ _ _ _ _ (Qc.[~(p,q)]) _ neq CONTL ).
      - by apply (deq_eq_where_notempty Qeq neqpq deqeq).
      - right; apply CIH; exists Qc; split;
          [by apply (contfree _ _ _ CONTL)
          |split; [by []| split; [|by[]]]].
        move: (g_wfcont_msg_inv wfco); elim=> neqq.
        elim=> nn it; apply: (it _ _ _ CONTL).
    * move=> wfco rfree qpro; move: (g_wfcont_msg_inv wfco); elim=> neqq.
      elim; elim=> L; elim=> Ty; elim=> G; elim=> CONTL wfcoG wfcoall.
      move: (qProject_None_inv L Ty G qpro); elim=> neq qpro0'.
      apply: qprj_none =>//=; move=> Lc Tyc Gc CONTLc; right.
      apply CIH; exists Q0.
      split; [by apply (rcv_Free_None_inv rfree CONTLc)| split].
      - move: (qProject_None_inv Lc Tyc Gc qpro); elim=> _.
        by move=> hp; apply hp.
      - by split; [apply (wfcoall _ _ _ CONTLc)|].
  Qed.

  Lemma RCV_Free_qProject_empty G :
    RCV_Free G -> g_wfcont G -> qProject G [fmap].
  Proof.
  have Qeq: exists (Q: {fmap role * role -> seq (lbl * mty) }), Q = [fmap].
    by exists [fmap].
  move: Qeq; elim=> Q Qeq; rewrite -Qeq.
  move=> hp1 hp2; move: (conj Qeq (conj hp1 hp2)) => {Qeq hp1 hp2}.
  move: G Q; apply /paco2_acc; move=> r0 _ CIH G Q.
  elim=> Qeq; elim; case: G.
  + by rewrite Qeq; move=> _ _; apply /paco2_fold; apply qprj_end.
  + move=> o FROM TO CONT rfree wfco; apply /paco2_fold.
    move: wfco rfree; case: o.
    * move=> L wfco rfree; move: (rfree FROM TO)=> contra.
      move: (rcv_Free_Some_inv contra); elim; rewrite eq_refl //=.
    * move=> wfco rfree; move: (g_wfcont_msg_inv wfco).
      elim=> neq; elim; elim=> Lc; elim=> Tyc; elim=> Gc.
      elim=> CONTLc wfcoc wfcoall.
      apply: qprj_none; [by []|].
      move=> L Ty G CONTL; right; apply CIH; split; [by []|].
      split;[| by apply (wfcoall _ _ _ CONTL)].
      move=> p q; move: (rfree p q) => rfreehp.
      by apply (rcv_Free_None_inv rfreehp CONTL).
  Qed.


  Inductive rcv_no (pq : role * role) : nat -> rg_ty -> Prop :=
  | rcv_no_0 G: rcv_Free pq G -> rcv_no pq 0 G
  | rcv_no_send n F T C:
    (forall L Ty G, C L = Some (Ty, G) -> rcv_no pq n G)
    -> rcv_no pq n (rg_msg None F T C)
  | rcv_no_rcv n L C Ty G:
    C L = Some (Ty, G) -> rcv_no pq n G ->
    rcv_no pq (n.+1) (rg_msg (Some L) pq.1 pq.2 C)
  .

SearchAbout rcv_no.

  (*Possible lemmas:
  - from GUnroll through steps exists n
  - boh*)


  (* *)
*)

End QProjection.
