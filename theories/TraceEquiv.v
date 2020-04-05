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

Section TraceEquiv.

(*Finite set to be thought of as the set of all participants involved in the protocol.*)
Variable PAR : {fset role}.

Definition PAR2 := (PAR `*` PAR)%fset.



  (*Definition Merge (F : lbl /-> mty * rl_ty) (L : rl_ty) : Prop :=
    forall Lb Ty L', F Lb = Some (Ty, L') -> EqL L' L.*)
 



(*In the following there is a problem, I think. However it is monotone...
  Definition qproj_rel := rg_ty -> {fmap role * role -> seq (lbl * mty) } -> Prop.
  Inductive qProj_ (*p p': role*) (r : qproj_rel) : qproj_rel :=
  | qprj_end : qProj_ r rg_end ([fmap qq:PAR2 => [::]])
  | qprj_none q q' CONT l Ty G Q:
      q != q' -> CONT l = Some (Ty, G) ->
      r (rg_msg None q q' CONT) Q ->
      qProj_ r (rg_msg (Some l) q q' CONT) Q
  | qprj_some q q' CONT l Ty G Q:
      q != q' -> CONT l = Some (Ty, G) ->
      r (rg_msg (Some l) q q' CONT) Q ->
      qProj_ r G (enq Q (q,q') (l, Ty))
  .
  Hint Constructors qProj_.
  Lemma Proj_monotone : monotone2 qProj_.
  Proof.
  rewrite /monotone2; move=> x0 x1 r r' it LE; move: it; case=>//.
  + move=> p p' CONT l Ty G Q neq CONTeq rel; apply: (qprj_none neq CONTeq).
    by apply (LE _ _ rel).
  + move=> p p' CONT l Ty G Q neq CONTeq rel; apply: (qprj_some neq CONTeq).
    by apply (LE _ _ rel).
  Qed. *)

(* first version: probably wrong.

  Definition qproj_rel := rg_ty -> {fmap role * role -> seq (lbl * mty) } -> Prop.
  Inductive qProj_ (r : qproj_rel) : qproj_rel :=
  | qprj_end : qProj_ r rg_end ([fmap qq:PAR2 => [::]])
  | qprj_none p p' CONT l Ty G Q:
      p != p' -> CONT l = Some (Ty, G) ->
      r (rg_msg (Some l) p p' CONT) Q ->
      qProj_ r (rg_msg None p p' CONT) Q
  | qprj_some p p' CONT l Ty G Q:
      p != p' -> CONT l = Some (Ty, G) ->
      r G (enq Q (p,p') (l, Ty)) ->
      qProj_ r (rg_msg (Some l) p p' CONT) Q
  .
  Hint Constructors qProj_.
  Lemma qProj_monotone : monotone2 qProj_.
  Proof.
  rewrite /monotone2; move=> x0 x1 r r' it LE; move: it; case=>//.
  + move=> p p' CONT l Ty G Q neq CONTeq rel; apply: (qprj_none neq CONTeq).
    by apply (LE _ _ rel).
  + move=> p p' CONT l Ty G Q neq CONTeq rel; apply: (qprj_some neq CONTeq).
    by apply (LE _ _ rel).
  Qed.
  Definition qProject CG Q := paco2 (qProj_) bot2 CG Q.*)

  Definition qproj_rel := rg_ty -> {fmap role * role -> seq (lbl * mty) } -> Prop.
  Inductive qProj_ (r : qproj_rel) : qproj_rel :=
  | qprj_end : qProj_ r rg_end ([fmap qq:PAR2 => [::]])
  | qprj_none p p' CONT (*l Ty G Q*) Q':
      p != p' -> 
      (forall l Ty G Q, CONT l = Some (Ty, G) ->
      (*deq Q (p, p') == Some ((l, Ty), Q') ->*)
      Q == enq Q' (p, p') (l, Ty) ->
      r (rg_msg (Some l) p p' CONT) Q ) ->
      qProj_ r (rg_msg None p p' CONT) Q'
  | qprj_some p p' CONT l Ty G Q Q':
      p != p' -> CONT l = Some (Ty, G) ->
      (*Q' == (enq Q (p,p') (l, Ty)) ->*)
      deq Q' (p, p') == Some ((l, Ty), Q) ->
      r G Q ->
      qProj_ r (rg_msg (Some l) p p' CONT) Q'
  .
  Hint Constructors qProj_.
  Lemma qProj_monotone : monotone2 qProj_.
  Proof.
  rewrite /monotone2; move=> x0 x1 r r' it LE; move: it; case=>//.
  + move=> p p' CONT Q' neq hp.
    apply: (qprj_none neq ); move=> l Ty G Q CONTeq enqu; apply LE.
    by apply: (hp l Ty G).
  + move=> p p' CONT l Ty G Q Q' neq CONTeq enqu rel.
    apply: (qprj_some neq CONTeq enqu); by apply (LE _ _ rel).
  Qed.
  Hint Resolve qProj_monotone.
  Definition qProject CG Q := paco2 (qProj_) bot2 CG Q.

About Project.

Open Scope fmap.


Print R_all.

  Inductive part_of: role -> rg_ty -> Prop :=
    | pof_from o F T C: part_of F (rg_msg o F T C)
    | pof_to o F T C: part_of T (rg_msg o F T C)
    | pof_cont p o F T C L G Ty: C L = Some (Ty, G) 
      -> part_of p G -> part_of p (rg_msg o F T C).


  Lemma part_of_label_label_aux p o o' F T C GG: 
    part_of p GG -> GG = rg_msg o F T C ->
        part_of p (rg_msg o' F T C).
  Proof.
  elim.
  + by move=> o0 F0 T0 C0 [hp1 hp2 hp3 hp4]; rewrite hp2; apply pof_from.
  + by move=> o0 F0 T0 C0 [hp1 hp2 hp3 hp4]; rewrite hp3; apply pof_to.
  + move=> p0 o0 F0 T0 C0 L G Ty contL partof ih [eq1 eq2 eq3 eq4].
    by rewrite -eq4; apply: (pof_cont o' F T contL partof).
  Qed.

  Lemma part_of_label_label p o o' F T C: 
    part_of p (rg_msg o F T C) ->
        part_of p (rg_msg o' F T C).
  Proof.
  by move=> hp; apply: (@part_of_label_label_aux p o o' F T C _ hp).
  Qed.


(*
translate p to something in the domain of L ()
*)
  Definition eProject (G: rg_ty) (E : {fmap role -> rl_ty}) : Prop :=
  (forall p, p \in PAR -> part_of p G -> 
      (exists L, Project p G L /\ E.[? p] = Some L)).



(*L to D and F; about the next 6 lemmas:
  - should be moved
  - might be be turned into 2 or even 0
*)

  Lemma qProject_end_inv_aux Q GG: 
    GG = rg_end -> qProject GG Q -> 
    Q = ([fmap qq:PAR2 => [::]]).
  Proof.
  move=> eq hp; punfold hp.
  move: hp eq => [||]//= [].
  Qed.

  Lemma qProject_end_inv Q:
  qProject rg_end Q -> 
    Q = ([fmap qq:PAR2 => [::]]).
  Proof.
  by apply qProject_end_inv_aux.
  Qed.


  Lemma qProject_None_inv_aux F T C l Ty G Q (*Q'*) GG: 
    GG = (rg_msg None F T C) ->
    qProject GG Q -> 
    F != T /\
    (C l = Some (Ty, G) ->
    (*deq Q' (F, T) == Some ((l, Ty), Q) /\*)
    (*Q' == enq Q (F, T) (l, Ty) ->*)
    qProject (rg_msg (Some l) F T C) (enq Q (F, T) (l, Ty))).
  Proof.
  move=> eq hp; punfold hp.
  move: hp eq => [|p p' CONT {}Q neq hp |]//= [].
  move=> eq1 eq2 eq3; split; [by rewrite -eq1 -eq2 | ].
  rewrite -eq1 -eq2 -eq3; move=> conteq.
  move: (hp _ _ _ (enq Q (p, p') (l, Ty)) conteq).
  by rewrite /upaco2 /qProject /bot2; elim.
  Qed.

  Lemma qProject_None_inv F T C l Ty G Q (*Q'*):
    qProject (rg_msg None F T C) Q -> 
    F != T /\
    (C l = Some (Ty, G) ->
    (*deq Q' (F, T) == Some ((l, Ty), Q) /\*)
    (*Q' == enq Q (F, T) (l, Ty) ->*)
    qProject (rg_msg (Some l) F T C) (enq Q (F, T) (l, Ty))).
  Proof.
  by apply: qProject_None_inv_aux.
  Qed.



  Lemma qProject_Some_inv_aux l F T C Q GG: 
    GG = (rg_msg (Some l) F T C) ->
    qProject GG Q -> 
    F != T /\
    (exists Ty G Q',
    C l = Some (Ty, G) /\
    (*Q == (enq Q' (F,T) (l, Ty)) /\*)
    deq Q (F, T) == Some ((l, Ty), Q') /\
    qProject G Q').
  Proof.
  move=> eq hp; punfold hp.
  move: hp eq  => [| | p p' CONT l0 Ty G {}Q Q' H0 H1 H2 H3] //= [].
  move=> H4 H5 H6 H7. split; [by rewrite -H5 -H6 | exists  Ty, G, Q].
  split; [by rewrite -H1 H7 H4 | split; [ by rewrite -H5 -H6 -H4|]].
  by move: H3; rewrite /upaco2 /qProject /bot2; elim.
  Qed.

  Lemma qProject_Some_inv l F T C Q:
    qProject (rg_msg (Some l) F T C) Q -> 
    F != T /\
    (exists Ty G Q', C l = Some (Ty, G) /\
    (*Q == (enq Q' (F,T) (l, Ty)) /\*)
    deq Q (F, T) == Some ((l, Ty), Q') /\
    qProject G Q').
  Proof.
  by apply: qProject_Some_inv_aux.
  Qed.

(*  Lemma enq_eval Q p p' L Ty: 
    (enq Q (p, p') (L, Ty)).[? (p, p')] = 
    match Q.
    Some [((L, Ty)) :: Q.[? (p, p')]).
  Proof.*)



(*  Lemma qProj_ext_eq_qProj G (Q Q': {fmap role * role -> seq (lbl * mty) }): 
    (forall p p', Q.[? (p, p')] = Q'.[? (p, p')]) ->
    qProject G Q -> qProject G Q'.
  Proof.
  move=> eqq prj; move: (conj eqq prj) => {eqq prj}.
  move=> /(ex_intro (fun Q=> _) Q) {Q}.
  move: G Q'; apply /paco2_acc; move=> r0 _ CIH G Q'.
  elim=> Q; elim; case G.
  + move=> exteq qpQ; rewrite /qProject in qpQ.
    punfold qpQ; move: qprj_end.
  Admitted.*)


  Lemma qProject_Some_cont_eq F T CONT Q L Ty G:
    qProject (rg_msg (Some L) F T CONT) Q ->
    CONT L = Some (Ty, G) -> qProject G Q.
  Admitted.


  Lemma qProject_None_cont_eq F T CONT Q L Ty G:
    qProject (rg_msg None F T CONT) Q ->
    CONT L = Some (Ty, G) -> qProject G Q.
  Proof.
  move=> qpro contL.
  move: (qProject_None_inv L Ty G  qpro).
  elim=> neq; rewrite contL; move=> qpro'_.
  have qpro': qProject (rg_msg (Some L) F T CONT) (enq Q (F, T) (L, Ty)).
    by apply qpro'_.
  move: (qProject_Some_inv qpro'); elim=> _; elim=> Ty0; elim=> G0.
  elim=> Q'; elim; rewrite contL; move=> [eqTy eqG]; elim=> eqQ.
  rewrite -eqTy /deq // in eqQ.

  Admitted.

(*again lemmas to be moved elsewhere later*)


  Lemma step_send_inv_aux F T C L Ty aa GG: 
    step aa GG (rg_msg (Some L) F T C) ->
    aa = a_send F T L Ty -> GG = rg_msg None F T C ->
    exists G, C L = Some (Ty, G).
  Proof.
  elim/step_ind => //=.
  + move=> L0 F0 T0 C0 Ty0 G eqC => [] [].
    move=> H0 H1 H2 H3 =>[] []. elim; elim; move=> H4.
    by exists G; rewrite -H2 -H3 -H4.
  + move=> a F0 T0 C0 C1 sub1 sub2 samed rall hp eqa => [] [].
    move=> eq1 eq2 eq3; move: sub1; rewrite eqa eq1 //=.
    by rewrite -(rwP negP) //=.
  Qed.

  Lemma step_send_inv F T C L Ty: 
    step (a_send F T L Ty) (rg_msg None F T C) (rg_msg (Some L) F T C) ->
    exists G, C L = Some (Ty, G).
  Proof.
  by move=> hp; apply: (step_send_inv_aux hp).
  Qed.

  Lemma step_qProject_send F T C L Ty Q:
    step (a_send F T L Ty) (rg_msg None F T C) (rg_msg (Some L) F T C) ->
    qProject (rg_msg None F T C) Q ->
    F != T /\ (exists G Q',
    C L = Some (Ty, G) /\ Q' == enq Q (F, T) (L, Ty) /\
    qProject (rg_msg (Some L) F T C) Q').
  Proof.
  move=> ste qpro.
  move: (step_send_inv ste); elim; move=> G eqcont.
  move: (@qProject_None_inv F T C L Ty G Q qpro).
  elim; move=> neq hp; split => //=.
  exists G, (enq Q (F, T) (L, Ty)); split; [|split; [ |apply hp]] =>//=.
  Qed.

  Lemma cProj_end_inv_aux p GG lT:
    Project p GG lT -> GG = rg_end ->
    lT = rl_end.
  Proof.
  by move=> hp; punfold hp; [move: hp => [] //=| by apply Proj_monotone].
  Qed.

  Lemma cProj_end_inv p lT:
    Project p rg_end lT -> lT = rl_end.
  Proof.
  by move=> hp; apply (cProj_end_inv_aux hp).
  Qed.

  Lemma cProj_send_none_inv_aux F T C GG lT:
    Project F GG lT -> GG = (rg_msg None F T C) ->
    F != T /\ (exists lC, lT = rl_msg l_send T lC /\ 
    same_dom C lC /\ R_all (upaco2 (Proj_ F) bot2) C lC).
  Proof.
  move=> hp; punfold hp; [move: hp => [] //=| by apply Proj_monotone].
  + move=> q gC lC neq samedom rall [eq1 eq2].
    by rewrite -eq1 -eq2; split; [| exists lC;  split; [ |]].
  + move=> o q gC lC neq samedom rall [eq1 eq2 eq3 eq4].
    by move: neq; rewrite eq2 -(rwP negP).
  + move=> o q s gC lC L neq1 neq2 neq3 samedom rall mer [eq1 eq2 eq3 eq4].
    by move: neq2; rewrite eq2 -(rwP negP).
  Qed.

  Lemma cProj_send_none_inv F T C lT: 
    Project F (rg_msg None F T C) lT ->
    F != T /\ (exists lC, lT = rl_msg l_send T lC /\ 
    same_dom C lC /\ R_all (upaco2 (Proj_ F) bot2) C lC).
  Proof.
  by move=> hp; apply: (cProj_send_none_inv_aux hp).
  Qed.

  Lemma eProject_send_none F T C E:
    F \in PAR -> eProject (rg_msg None F T C) E ->
    F != T /\ (exists lC, E.[? F]%fmap = Some (rl_msg l_send T lC) /\ 
    same_dom C lC /\ R_all (Project F) C lC).
  Proof.
  rewrite /eProject; move=> Fin hp; move: (hp _ Fin).
  move=> hp_part; move: (hp_part (pof_from None F T C)).
  elim; move=> lT; elim; move=> pro eq; move: (cProj_send_none_inv pro).
  elim; move=> neq; elim; move=> lC; elim; move=> lTeq; elim; move=> samedom rall.
  split; [by []|exists lC]; split; [by rewrite eq; apply f_equal| split; [ by []|]].
  move: rall; rewrite /R_all; move=> rall L Ty G lTT someg somel.
  move: (rall _ _ _ _ someg somel).
  by rewrite /upaco2 /Project /bot2; elim.
  Qed.


  Lemma cProj_send_some_inv_aux L F T C GG lT:
    Project F GG lT -> GG = (rg_msg (Some L) F T C) ->
    F != T /\ (exists lC Ty, lC L = Some (Ty, lT) /\ 
    same_dom C lC /\ R_all (upaco2 (Proj_ F) bot2) C lC).
  Proof.
  move=> hp; punfold hp; [move: hp => [] //=| by apply Proj_monotone].
  + move=> l Ty q gC lC lT0 neq samedom rall Cleq [eq1 eq2 eq3].
    by rewrite -eq1 -eq2 -eq3; split; [| exists lC, Ty; split; [|split]].
  + move=> o q gC lC neq samedom rall [eq1 eq2 eq3 eq4].
    by move: neq; rewrite eq2 -(rwP negP).
  + move=> o q s gC lC L0 neq1 neq2 neq3 samedom rall mer [eq1 eq2 eq3 eq4].
    by move: neq2; rewrite eq2 -(rwP negP).
  Qed.

  Lemma cProj_send_some_inv L F T C lT: 
    Project F (rg_msg (Some L) F T C) lT ->
    F != T /\ (exists lC Ty, lC L = Some (Ty, lT) /\ 
    same_dom C lC /\ R_all (upaco2 (Proj_ F) bot2) C lC).
  Proof.
  by move=> hp; apply: (cProj_send_some_inv_aux hp).
  Qed.

  Lemma eProject_send_some L F T C E:
    F \in PAR -> eProject (rg_msg (Some L) F T C) E ->
    F != T /\ (exists lC Ty lT, lC L = Some (Ty, lT) /\
    E.[? F]%fmap = Some lT /\ same_dom C lC /\ R_all (Project F) C lC).
  Proof.
  rewrite /eProject; move=> Fin hp; move: (hp _ Fin).
  move=> hp_part; move: (hp_part (pof_from (Some L) F T C)).
  elim; move=> lT; elim; move=> pro eq; move: (cProj_send_some_inv pro).
  elim; move=> neq; elim; move=> lC; elim; move=> Ty; elim; move=> lCLeq.
  elim; move=> samedom rall; split; [by []|exists lC, Ty, lT].
  split; [by []| split; [ by []|split; [by []|]]].
  move: rall; rewrite /R_all; move=> rall L0 Ty0 G lTT someg somel.
  move: (rall _ _ _ _ someg somel).
  by rewrite /upaco2 /Project /bot2; elim.
  Qed.


  Lemma cProj_recv_inv_aux olb F T C GG lT:
    Project T GG lT -> GG = (rg_msg olb F T C) ->
    F != T /\ (exists lC, lT = rl_msg l_recv F lC /\ 
    same_dom C lC /\ R_all (upaco2 (Proj_ T) bot2) C lC).
  Proof.
  move=> hp; punfold hp; [move: hp => [] //=| by apply Proj_monotone].
  + move=> q gC lC neq samedom rall [eq1 eq2 eq3].
    by move: neq; rewrite eq3 -(rwP negP).
  + move=> lb0 Ty q gC lC lT0 neq samedom rall cLeq [eq1 eq2 eq3 eq4].
    by move: neq; rewrite eq3 -(rwP negP).
  + move=> o q gC lC neq samedom rall [eq1 eq2 eq3].
    by rewrite -eq2 -eq3; split; [rewrite eq_sym| exists lC; split; [ | split; [|]]].
  + move=> o q s gC lC L neq1 neq2 neq3 samedom rall mer [eq1 eq2 eq3 eq4].
    by move: neq3; rewrite eq3 -(rwP negP).
  Qed.

  Lemma cProj_recv_inv  olb F T C lT: 
    Project T (rg_msg olb F T C) lT ->
    F != T /\ (exists lC, lT = rl_msg l_recv F lC /\ 
    same_dom C lC /\ R_all (upaco2 (Proj_ T) bot2) C lC).
  Proof.
  by move=> hp; apply: (cProj_recv_inv_aux hp).
  Qed.

  Lemma eProject_recv o F T C E:
    T \in PAR -> eProject (rg_msg o F T C) E ->
    F != T /\ (exists lC, E.[? T]%fmap = Some (rl_msg l_recv F lC) /\ 
    same_dom C lC /\ R_all (Project T) C lC).
  Proof.
  rewrite /eProject; move=> Fin hp; move: (hp _ Fin).
  move=> hp_part; move: (hp_part (pof_to o F T C)).
  elim; move=> lT; elim; move=> pro eq; move: (cProj_recv_inv pro).
  elim; move=> neq; elim; move=> lC; elim; move=> lTeq. (*; elim; move=> lCLeq.*)
  elim; move=> samedom rall; split; [by []|exists lC].
  split; [by rewrite -lTeq | split; [ by []|]].
  move: rall; rewrite /R_all; move=> rall L0 Ty0 G lTT someg somel.
  move: (rall _ _ _ _ someg somel).
  by rewrite /upaco2 /Project /bot2; elim.
  Qed.



  Lemma cProj_mrg_inv_aux p olb F T C GG lT:
    Project p GG lT -> 
    p != F -> p != T -> GG = rg_msg olb F T C -> 
    F != T /\ (exists lC, same_dom C lC /\
      R_all (upaco2 (Proj_ p) bot2) C lC /\
      Merge lC lT).
  Proof.
  move=> hp; punfold hp; [move: hp => [] //=| by apply Proj_monotone].
  + move=> q gC lC neq samedom rall neqF neqT [eq1 eq2 eq3 eq4].
    by move: neqF; rewrite eq2 -(rwP negP).
  + move=> lb Ty q gC lC lT0 neq samedom rall lCeq neqF neqT [eq1 eq2 eq3 eq4].
    by move: neqF; rewrite eq2 -(rwP negP).
  + move=> o q gC lC neq samedom rall neqF neqT [eq1 eq2 eq3 eq4].
    by move: neqT; rewrite eq3 -(rwP negP).
  + move=> o q s gC lC lT0 neq1 neq2 neq3 samedom rall mer neqF neqT [eq1 eq2 eq3 eq4].
    split; [by move: neq1; rewrite eq2 eq3|exists lC].
    by rewrite -eq4; split; [ |split; [|]].
  Qed.

  Lemma cProj_mrg_inv p olb F T C lT:
    Project p (rg_msg olb F T C) lT ->
    p != F -> p != T ->
    F != T /\ (exists lC, same_dom C lC /\
      R_all (upaco2 (Proj_ p) bot2) C lC /\
      Merge lC lT).
  Proof.
  by move=> hp neq1 neq2; apply: (cProj_mrg_inv_aux hp neq1 neq2).
  Qed.

  Lemma EqL_r_end_inv_aux lT lT': 
    EqL lT lT' -> lT' = rl_end -> lT = rl_end.
  Proof.
  by move=> hp; punfold hp; move: hp => [] //=.
  Qed.

  Lemma EqL_r_end_inv lT: 
    EqL lT rl_end -> lT = rl_end.
  Proof.
  by move=> hp; apply (EqL_r_end_inv_aux hp).
  Qed.

  Lemma EqL_r_msg_inv_aux lT lT' a p C': 
    EqL lT lT' -> lT' = rl_msg a p C' ->
    exists C, same_dom C C' /\ 
       R_all EqL C C' /\ lT = rl_msg a p C.
  Proof.
  move=> hp; punfold hp; move: hp => [] //=.
  move=> a0 p0 C1 C2 samed rall [eq1 eq2 eq3].
  exists C1; rewrite eq1 eq2 -eq3; split; [|split] => //=.
  rewrite /R_all; move=> L Ty lT1 lT2 ceq1 ceq2.
  rewrite /R_all in rall; move: (rall L Ty lT1 lT2 ceq1 ceq2).
  by rewrite /upaco2; elim; rewrite //=.
  Qed.
  
  Lemma EqL_r_msg_inv a p C' lT: 
    EqL lT (rl_msg a p C') ->
    exists C, same_dom C C' /\ 
       R_all EqL C C' /\ lT = rl_msg a p C.
  Proof.
  by move=> hp; apply: (EqL_r_msg_inv_aux hp).
  Qed.

(*to be moved in Local.v*)

  Lemma EqL_trans lT1 lT2 lT3:
    EqL lT1 lT2 -> EqL lT2 lT3 -> EqL lT1 lT3.
  Proof.
  move=> hp1 hp2; move: (conj hp1 hp2) => {hp1 hp2}.
  move=> /(ex_intro (fun lT=> _) lT2) {lT2}; move: lT1 lT3.
  apply /paco2_acc; move=> r0 _ CIH lT1 lT3; elim=> lT2.
  elim; case: lT3 =>//=.
  + move=> eql12 eql23; move: (EqL_r_end_inv eql23) eql12 =>->.
    move=> eql12; move: (EqL_r_end_inv eql12) =>->.
    by apply /paco2_fold; apply el_end.
  + move=> a r C eql12 eql23; move: (EqL_r_msg_inv eql23).
    elim=> C2; elim=> samed23; elim=> rall23 lT2eq.
    rewrite lT2eq in eql12; move: (EqL_r_msg_inv eql12).
    elim=> C1; elim=> samed12; elim=> rall12 lT1eq.
    rewrite lT1eq; apply /paco2_fold; apply el_msg.
    - rewrite /same_dom; rewrite /same_dom in samed12 samed23.
      by move=> L Ty; rewrite (samed12 L Ty).
    - rewrite /R_all; move=> L Ty cT1 cT3 C1L C3L.
      rewrite /upaco2; right; apply CIH.
      have cT2aux: exists cT2, C2 L = Some (Ty, cT2).
        rewrite /same_dom in samed12; rewrite -(samed12 L Ty).
        by exists cT1.
      move: cT2aux; elim=> cT2 C2L; exists cT2.
      rewrite /R_all in rall12 rall23.
      by split; [apply (rall12 L Ty)|apply (rall23 L Ty)].
  Qed.



  Lemma EqL_Project p G lT lT': 
    EqL lT lT' -> Project p G lT -> Project p G lT'.
  Proof.
  move=> eql prj; move: (conj eql prj) => {eql prj}.
  move=> /(ex_intro (fun lT=> _) lT) {lT}.
  move: G lT'; apply /paco2_acc; move=> r0 _ CIH G lT'.
  elim=> lT; elim; case lT'.
  + move=> eql; move: (EqL_r_end_inv eql); move=>->.
    rewrite /Project; move=> pro; move: paco2_mon; rewrite /monotone2.
    by move=> pamo; apply (pamo _ _ _ _ _ _ _ pro).
  + move=> a q C eql; move: (EqL_r_msg_inv eql).
    elim=> C0; elim=> samed; elim=> rall lTeq; rewrite lTeq.
    case G; [by move => hp; move: (cProj_end_inv hp)|].
    move=> op F T CONT; case: (@eqP _ p F).
    * move=> pF; rewrite pF; case: op.
      - move=> L hpro; move: (cProj_send_some_inv hpro); elim=> neq.
        elim=> lC0; elim=> Ty; elim=> lC0eq; elim=> sam ral.
        apply /paco2_fold.
        apply: (@prj_send2 _ _ _ Ty _ _ (extend L (Ty, rl_msg a q C) lC0))=>//=.
        + have exCONT: exists GG, CONT L = Some (Ty, GG).
            rewrite /same_dom in sam; move: (sam L Ty); elim=> _ sam'.
            by apply sam'; exists (rl_msg a q C0).
          move: exCONT; elim; move=> GG contL.
          by apply: (same_dom_extend_some_l (rl_msg a q C) sam contL).
        + rewrite /R_all; move=> LL Tyy GG lTT contLL; rewrite /extend.
          case: ifP.
          * rewrite -(rwP eqP); move=> eqLLL [eq1 eq2].
            rewrite /upaco2; right; apply CIH; rewrite -eq2.
            exists (rl_msg a q C0); split; [by rewrite -lTeq|].
            rewrite /R_all in ral; rewrite -eq1 -eqLLL in contLL. 
            move: (ral _ _ _ _ contLL lC0eq); rewrite /upaco2.
            elim; [by rewrite pF |by []].
          * move=> neqLLL lC0LL; rewrite /R_all in ral.
            move: upaco2_mon; rewrite /monotone2; move=> up.
            apply (up _ _ _ _ _ _ _ (ral _ _ _ _ contLL lC0LL)).
            by rewrite /bot2.
        + by rewrite /extend; case: ifP; [|rewrite eq_refl].
      - move=> hpro; move: (cProj_send_none_inv hpro); elim=> neq.
        elim=> lC0; elim; move=> [eq1 eq2 eq3]; elim=> samed0 ral.
        apply /paco2_fold; rewrite eq1 eq2.
        apply (prj_send1 neq).
        + rewrite /same_dom; rewrite /same_dom in samed samed0.
          by move=> LL Tyy; rewrite (samed0 LL Tyy) -eq3.
        + rewrite /R_all; move=> LL Tyy GG lTT contLL lcontLL.
          rewrite /upaco2; right; apply CIH.
          have lT0aux: exists lT0, C0 LL = Some (Tyy, lT0).
            rewrite /same_dom in samed; rewrite (samed LL Tyy).
            by exists lTT.
          move: lT0aux; elim=> lT0 lcont0LL; exists lT0.
          split; rewrite /R_all in rall ral; [by apply (rall LL Tyy)|].
          rewrite eq3 in lcont0LL; move: (ral _ _ _ _ contLL lcont0LL).
          by rewrite /upaco2 pF; elim=> //=.
    * rewrite (rwP eqP) (rwP negP); move=> neq; case: (@eqP _ p T).
      - move=> pT; rewrite pT; move=> hpro.
        move: (cProj_recv_inv hpro); elim=> neqFT; elim=> lC; elim.
        move=> [eq1 eq2 eq3]; elim=> samed0 ral; apply /paco2_fold.
        rewrite eq_sym in neqFT.
        rewrite eq1 eq2; apply: (prj_recv _ neqFT).
        + rewrite /same_dom; rewrite /same_dom in samed samed0.
          by move=> LL Tyy; rewrite (samed0 LL Tyy) -eq3.
        + rewrite /R_all; move=> LL Tyy GG lTT contLL lcontLL.
          rewrite /upaco2; right; apply CIH.
          have lT0aux: exists lT0, C0 LL = Some (Tyy, lT0).
            rewrite /same_dom in samed; rewrite (samed LL Tyy).
            by exists lTT.
          move: lT0aux; elim=> lT0 lcont0LL; exists lT0.
          split; rewrite /R_all in rall ral; [by apply (rall LL Tyy)|].
          rewrite eq3 in lcont0LL; move: (ral _ _ _ _ contLL lcont0LL).
          by rewrite /upaco2 pT; elim=> //=.
      - rewrite (rwP eqP) (rwP negP); move=> neqpT hpro.
        move: (cProj_mrg_inv hpro neq neqpT); elim=> neqFT.
        elim=> lC0; elim=> samed0; elim=> ral mer.
        apply /paco2_fold.
        apply: (@prj_mrg _ _ _ _ _ _ 
          (same_dom_const CONT (rl_msg a q C)) _ neqFT neq neqpT).
        + by apply same_dom_const_same_dom.
        + rewrite /R_all; move=> LL Tyy GG lTT contLL lcontLL.
          rewrite /upaco2; right; apply CIH.
          have lT0aux: exists lT0, lC0 LL = Some (Tyy, lT0).
            rewrite /same_dom in samed0; rewrite -(samed0 LL Tyy).
            by exists GG.
          have lTTeq : lTT = (rl_msg a q C).
            rewrite /same_dom_const contLL in lcontLL.
            by move: lcontLL=> [].
          rewrite lTTeq; move: lT0aux; elim=> lT0 lcont0LL.
          exists lT0; split.
          * rewrite /Merge in mer; move: (mer _ _ _ lcont0LL).
            move=> eql_1; apply: (EqL_trans eql_1).
            rewrite /EqL; apply /paco2_fold; apply (el_msg _ _ samed).
            move: rall; rewrite /R_all /upaco2.
            move=> rall Le Tye lTe0 lTe eqe0 eqe; left.
            by apply: (rall _ _ _ _ eqe0 eqe).
          * rewrite /R_all in ral; move: (ral _ _ _ _ contLL lcont0LL).
            by rewrite /upaco2; elim.
          * rewrite /Merge; move=> Ln Tn lTn sdc.
            move: (same_dom_const_some sdc) =>-> //=.
  Qed.

(*Next thing should be moved in Global.v*)


  Definition g_pr :=  rg_ty -> Prop.
  Inductive g_wform_ (P : g_pr) : g_pr :=
  | g_wform_end : g_wform_ P rg_end
  | g_wform_msg o F T C L Ty G:
      C L = Some (Ty, G) -> P G ->
      (forall LL TTy GG, 
        C LL = Some (TTy, GG) -> P GG) ->
      g_wform_ P (rg_msg o F T C).
  Hint Constructors g_wform_.
  Definition g_wform g := paco1 g_wform_ bot1 g.

  Lemma g_wform_monotone : monotone1 g_wform_.
  Proof.
  rewrite /monotone1; move=> G P P'; case=>//=.
  move=> o F T C L Ty G0 CLeq wfG wfall hp.
  apply (g_wform_msg _ _ _ CLeq); [by apply hp|].
  move=> LL TTy GG CLL; apply hp.
  by apply (wfall _ _ _ CLL).
  Qed.
  Hint Resolve g_wform_monotone.

  Lemma g_wform_msg_inv_aux GG o F T C: 
    g_wform GG -> GG = (rg_msg o F T C)->
    (exists L Ty G, C L = Some (Ty, G) /\ g_wform G) /\
    (forall LL TTy GG, C LL = Some (TTy, GG) -> g_wform GG).
  Proof.
  move=> wf; rewrite /g_wform in wf; punfold wf.
  move: wf =>
    [|o' F' T' C' L Ty G CL hp hpall [eq1 eq2 eq3 eq4]] //=.
  split.
  + exists L, Ty, G; split; [by rewrite -eq4|].
    by move: hp; rewrite /upaco1; elim.
  + move=> LL TTy GG' CLL; rewrite -eq4 in CLL.
    by move: (hpall _ _ _ CLL); rewrite /upaco1; elim.
  Qed.

  Lemma g_wform_msg_inv o F T C: 
    g_wform (rg_msg o F T C)->
    (exists L Ty G, C L = Some (Ty, G) /\ g_wform G) /\
    (forall LL TTy GG, C LL = Some (TTy, GG) -> g_wform GG).
  Proof.
  by move=> hp; apply (@g_wform_msg_inv_aux _ o F T _ hp).
  Qed.




  Lemma step_ind_str (P : act -> rg_ty -> rg_ty -> Prop) :
    (forall L F T C Ty G, C L = Some (Ty, G) ->
      P (a_send F T L Ty) (rg_msg None F T C) (rg_msg (Some L) F T C))
    ->
    (forall L F T C Ty G, C L = Some (Ty, G) -> 
      P (a_recv F T L Ty) (rg_msg (Some L) F T C) G)
    ->
    (forall a F T C0 C1, subject a != F -> subject a != T ->
      same_dom C0 C1 -> R_all (step a) C0 C1 ->
      R_all (P a) C0 C1 ->
        P a (rg_msg None F T C0) (rg_msg None F T C1))
    ->
    (forall a L F T C0 C1, subject a != T ->
      same_dom C0 C1 -> R_only (step a) L C0 C1 ->
      (*new property, mirroring R_only*)
      R_only (P a) L C0 C1 ->
      P a (rg_msg (Some L) F T C0) (rg_msg (Some L) F T C1)) 
  -> forall (a : act) (G G' : rg_ty), step a G G' -> P a G G'.
  Proof.
  move=> P_send P_recv P_amsg1 P_amsg2; fix Ih 4.
  move=> a G G'; case =>//=.
  + move=> a' F T C0 C1 nF nT samed rall.
    apply: P_amsg1 =>//=; move: rall; rewrite /R_all.
    move=> rall L Ty G0 G1 C0L C1L; apply Ih.
    by apply (rall _ _ _ _ C0L C1L).
  + move=> a' L F T C0 C1 nT samed ronly.
    apply: P_amsg2 =>//=; move: ronly; rewrite /R_only.
    elim=> cond; elim=> Ty; elim=> G0; elim=> G1.
    elim=> C0L; elim=> C1L step; split; [by []|].
    exists Ty, G0, G1; split; [by []|split; [by []|]].
    by apply Ih.
  Qed.

  Lemma step_subject_part_of a G G':
    step a G G' -> g_wform G -> part_of (subject a) G.
  Proof.
  elim/step_ind_str.
  + move=> L F T C Ty G0 CL wf; rewrite /subject.
    by apply pof_from.
  + move=> L F T C Ty G0 CL wf; rewrite /subject.
    by apply pof_to.
  + move=> a0 F T C0 C1 nF nT sd ra ih wf.
    move: (g_wform_msg_inv wf); elim; elim=> L; elim=> Ty.
    elim=> G0; elim=> C0L wf0 wfall0; apply: (pof_cont _ _ _ C0L).
    have G1_aux: exists G1, C1 L = Some (Ty, G1).
      by rewrite /same_dom in sd; apply sd; exists G0.
    move: G1_aux; elim=> G1 C1L.
    by apply (ih _ _ _ _ C0L C1L).
  + move=> a0 L F T C0 C1 nT sd ron ronpof wf.
    case: (@eqP _ (subject a0) F).
    - by move => sa0F; rewrite sa0F; apply pof_from.
    - rewrite (rwP eqP) (rwP negP); move=> sa0F.
      move: (g_wform_msg_inv wf); elim; elim=> L0; elim=> Ty.
      elim=> G0; elim=> C0L wf0 wfall0.
      rewrite /R_only in ronpof; move: ronpof; elim=> hp.
      elim=> Ty0; elim=> G0'; elim=> G1'; elim=> C0L'.
      elim=> C1L' ih0; apply: (pof_cont  _ _ _ C0L').
      by apply: ih0; apply: (wfall0 _ _ _ C0L').
  Qed.

(*g_wform to be added as a hypothesis*)
  Lemma Project_step G Q E a G':
    step a G G' -> g_wform G ->
    (forall p, part_of p G -> p \in PAR)-> 
    qProject G Q -> eProject G E
    -> exists E' Q', qProject G' Q' /\ eProject G' E'
       /\ lstep a (E, Q) (E', Q').
  Proof.
  elim/step_ind_str.
  + move=> L F T C Ty G0 contL wf pin qpro epro.
    have Fin: F \in PAR.
      by apply: pin; apply: pof_from.
    move: (@eProject_send_none F T C E Fin epro); elim; move=> neq.
    elim=> lC; elim=> envF; elim=> samedom rall.
    move: (qProject_None_inv L Ty G0 qpro).
    elim; elim; move=> qpro0; move: (qpro0 contL)=> {}qpro0.
    have lT_aux: exists lT, lC L = Some (Ty, lT).
      move: samedom; rewrite /same_dom; move=> sd; rewrite -sd.
      by exists G0.
    move: lT_aux; elim=> lT lcontL.
    exists (E.[F <- lT]), (enq Q (F, T) (L, Ty)).
    split; [by apply qpro0|split].
    * move: epro; rewrite /eProject; move=> it p.
      case: (@eqP _ p F).
      - move =>->; elim; exists lT; split.
        + rewrite /Project; apply /paco2_fold.
          apply: (@prj_send2 F (upaco2 (Proj_ F) bot2) L Ty T C lC lT) => //=.
          move: rall; rewrite /Project /R_all /upaco2.
          by move=> hp L0 Ty0 G1 T1 hp1 hp2; left; apply (hp _ _ _ _ hp1 hp2).
        + by rewrite fnd_set; case: ifP; rewrite eq_refl //=.
      - rewrite (rwP eqP); rewrite fnd_set; case: ifP =>//=.
        move=> hp1 hp2 hp3 hp4;  move: (it _ hp3 (part_of_label_label _ hp4)).
        elim; move=> L0; elim=> pro_p E_p; exists L0; split; [| by []].
        case: (@eqP _ p T).
        + move=> pT; move: pro_p; rewrite pT;  move=> pro_T.
          rewrite /Project; apply /paco2_fold.
          move: (@cProj_recv_inv _ _ _ _ _ pro_T); elim; rewrite eq_sym.
          move=>neq2; elim=> lC0; elim=> L0eq; elim=> samed ral.
          by rewrite L0eq; apply: (prj_recv (Some L) neq2 samed ral).
        + rewrite (rwP eqP)=> neqpT; rewrite /Project; apply /paco2_fold.
          move: hp1; rewrite (rwP negPf)=> neqpF.
          move: neqpT; rewrite (rwP negP)=> neqpT.
          move: (cProj_mrg_inv pro_p neqpF neqpT); elim; elim; elim=> lC0.
          elim=> samed; elim=> ral mer.
          by apply: (prj_mrg _ neq neqpF neqpT samed ral mer).
    * apply: ls_send =>//=; rewrite /do_act envF lcontL=> //=.
      by case: ifP; rewrite! eq_refl =>//=.
  + move=> L F T C Ty G0 contL wf pin qpro epro.
    have Tin: T \in PAR.
      by apply: pin; apply: pof_to.
    move: (@eProject_recv _ F T C E Tin epro); elim=> neq.
    elim=> lC; elim=> envT; elim=> samedom rall.
    move: (qProject_Some_inv qpro); elim; elim.
    elim=> Ty0; elim=> GG; elim=> Q'.
    elim; rewrite contL; move=> [eqTy eqG0]; rewrite eqTy eqG0.
    elim=> deqeq qpro'.
    have lT_aux: exists lT, lC L = Some (Ty, lT).
      move: samedom; rewrite /same_dom; move=> sd; rewrite -sd.
      by exists G0.
    move: lT_aux; elim=> lT lcontL.
    exists (E.[T <- lT]), Q'.
    split; [by apply qpro' | split].
    * move: epro; rewrite /eProject; move=> it p.
      case: (@eqP _ p T).
      - move =>->; elim; exists lT; split.
        + move: rall contL; rewrite /R_all eqG0; move=> rallu contL.
          by apply: (rallu _ _ _ _ contL lcontL).
        + by rewrite fnd_set; case: ifP; rewrite eq_refl //=.
      - rewrite (rwP eqP); rewrite fnd_set; case: ifP =>//=.
        move=> hp1 hp2 hp3 hp4; move: contL; rewrite eqG0; move=> contL.
        move: (it p hp3 (pof_cont (Some L) F T contL hp4)).
        elim=> L0; elim=> pro_p E_p; exists L0; split; [| by []].
        case: (@eqP _ p F).
        + move=> pF; move: pro_p; rewrite pF; move=> pro_F.
          rewrite /Project; apply /paco2_fold.
          move: (@cProj_send_some_inv _ _ _ _ _ pro_F); elim; elim.
          elim=> lC0; elim=> Ty1; elim=> lcontL0; elim=> samed ral.
          have eqTy1: Ty1 = Ty.
            rewrite /same_dom in samed.
            move: (samed L Ty); elim=> sd1 sd2; move: sd1. 
            by elim; [ rewrite lcontL0; move=> L0' [d0 d1]|exists GG].
          rewrite eqTy1 in lcontL0; rewrite /R_all in ral.
          apply paco2_unfold; [by apply Proj_monotone| ].
          by move: (ral _ _ _ _ contL lcontL0); rewrite /upaco2; elim.
        + rewrite (rwP eqP)=> neqpF.
          move: hp1; rewrite (rwP negPf)=> neqpT.
          move: neqpF; rewrite (rwP negP)=> neqpF.
          move: (cProj_mrg_inv pro_p neqpF neqpT); elim; elim; elim=> lC0.
          elim=> samed; rewrite /R_all /Merge /EqL; elim=> ral mer.
          have lT'aux: exists lT', lC0 L = Some (Ty, lT').
            by rewrite /same_dom in samed; rewrite -samed; exists GG.
          move: lT'aux; elim=> lT' lcont0L.
          apply: (@EqL_Project _ _ lT'); [by apply (mer _ _ _ lcont0L)|].
          by move: (ral _ _ _ _ contL lcont0L); rewrite /upaco2; elim.
    * apply: ls_recv =>//=; rewrite /do_act envT lcontL eqTy => //=.
      by case: ifP; rewrite! eq_refl =>//=.
  + move=> aa F T C0 C1 nF nT sd01 r01 IH wf pin qpro epro.
    have subjin: subject aa \in PAR.
      apply: pin.
      apply: (@step_subject_part_of _ _ (rg_msg None F T C1)); [|by []].
      by apply: st_amsg1.
    move: (g_wform_msg_inv wf); elim; elim=> L; elim=> Ty; elim=> G0.
    elim=> C0L wf0 wfcont0.
    (*E' = any of the E' in the IH*)
    
  Admitted.




  Definition step_equiv G P :=
    forall a, (exists G', step a G G') <-> (exists P', lstep a P P').

  Fail Lemma g_stequiv G E Q :
    proj_cfg G == Some (E, Q) ->
    step_equiv G (E, Q).
  (*
  Proof.
    rewrite /step_equiv/proj_cfg.
    case G_E: (proj_env G) => [E'|//].
    case G_Q: (queue_contents G [fmap]%fmap) => [Q'|//].
    move=>/eqP=>[[EE' QQ']].
    move: EE' QQ' G_E G_Q=>->->/eqP-H1/eqP-H2 a; split.
    (* Testing *)
    move=>[G']. elim=>//.
    About step_ind1.
    (* End Testing *)
    - move=>[G' H]; move: G H H1 H2; elim/gty_ind1=>//.
      + by move=> St; case Eq: (g_end (option lbl)) _ / St =>//.
      + by move=> v St; case Eq: (g_var (option lbl) v) _ / St =>//.
      + move=> G Ih.
        admit.
      + move=> lb p q Ks Ih.
        admit.
        (*
        move=> lb p q Ks t Gp Cont Proj Queue.
        move: (proj_send Proj) => [KsL] /andP-[Ks_KsL E_KsL].
        move: (lookup_prjall Cont Ks_KsL) => [Lp /andP-[Gp_Lp KsL_Lp]].
        move: (doact_send E_KsL KsL_Lp) => [E'' E_send].
        by exists (E'', enq Q (p, q) (lb, t)); constructor.
         *)
    - admit.
  Admitted.
   *)

  (*
  Inductive Roll : renv -> renv -> Prop :=
  | RR : forall p P Q,

  Definition trace_equiv G P : Prop :=
    forall tr, g_lts tr G <-> l_lts tr P.

   *)
  Fail Lemma g_trequiv G : forall P, proj_cfg G == Some P -> trace_equiv G P.
  (*
  Proof.
    move=>[E Q]; rewrite /trace_equiv/proj_cfg.
    case G_E: (proj_env G) => [E'|//].
    case G_Q: (queue_contents G [fmap]%fmap) => [Q'|//].
    move=>/eqP=>[[EE' QQ']].
    move: EE' QQ' G_E G_Q=>->->/eqP-H1/eqP-H2 tr; split.

    cofix Ch.
    + move=> trcG; move: trcG H1 H2 Ch; case.
      * rewrite /proj_env/= =>/eqP-[<-] /eqP-[<-] _; constructor.
      * move=> a t G0 G' step trc.
      * move=>/=. _.
   *)

  Fail Definition q_projection G :=
    if is_valid G then q_project G (rg_parts G)
    else None.

  Fail Lemma g_stequiv G :
    forall (P : MsgQ * seq (role * l_ty)),
    Projection G P ->
    step_equiv G P.
  (*
  Proof.
    rewrite /step_equiv/Projection => [[Q P]/= [Parts G_P] a]; split.
    - move=> [G' H]; move: H Parts G_P; elim =>///=.
      - move=>[[p q] ty]/= {G}G Parts.
      (* Lemmas about q_projection to simplify these proofs: e.g.
         if q_projection (rg_msg p G) == Some (Q, P) ->
            msg_proj G p == Some Qp &&
            msg_proj G q == Some Qq &&
            Q == Qp ++ Qq &&
            q_proj G p == Some Lp &&
            q_proj G q == Some Lq &&
            q_projection G == Some (Q', P') &&
            Q == Qp ++ Qq ++ Q' &&
            P == (p, Lp) :: (q, Lq) :: Some (Q', P')

          Maybe the better option is to reflect q_projection as an inductive
          predicate relating
      *)
      admit.
    - move=> [[Q' P']].
      admit.
  Admitted.
   *)

  (*
  Lemma st_valid a G G' :
    is_valid G -> step a G G' -> is_valid G'.
  Proof.
  Admitted.
   *)

  Fail Lemma g_stproj a G G' :
    forall (P P' : MsgQ * seq (role * l_ty)),
    q_projection G == Some P ->
    step a G G' ->
    lstep a P P' ->
    q_projection G' == Some P'.
  (*
  Proof.
  Admitted.
   *)

  Fail Lemma qproj_end G :
    q_projection G == Some ([::], [::]) ->
    G = rg_end.
  (*
  Proof.
    rewrite /q_projection.
    elim: {-1} (rg_parts G) (eq_refl (rg_parts G)) =>//.
    + elim/rgty_ind2: G=>///= G; case: (is_valid G) =>//.
      by move=> Ih /Ih/(_ (eq_refl _))->; rewrite eq_refl.
    + move=> p rs Ih/= _.
      case: (is_valid G); case: (q_proj G p); case: (q_project G rs) =>//.
      - move=>[Q P] [Q' L] /eqP-[QQ]; case: P=>// [l' L'].
        by rewrite /insert/=; case: ifP=>/=// _; case: (lookup p L').
      - by move=>[Q P].
  Qed.
   *)

  Fail Lemma g_trequiv G :
    forall (P : MsgQ * seq (role * l_ty)),
    q_projection G == Some P ->
    trace_equiv G P.
  (*
  Proof.
  (*   move=> P H; rewrite /trace_equiv=> tr; split. *)
  (*   - move: tr G P H; cofix Ch; move=> tr G P H; case: tr. *)
  (*     + move=> H1; elim/glts_inv: H1=>// _ _ Eq; move: Eq H=><-/=. *)
  (*       by rewrite /q_projection/==>/eqP-[<-]; constructor. *)
  (*     + move=> a t; elim/glts_inv=>// _ a' t' G0 G' aG tG' [aa' tt' _ {G0}]. *)
  (*       move: aa' aG=>->aG {a'}. *)
  (*       move: tt' tG'=>->tG' {t'}. *)
  (*       move: (g_stequiv H) => /(_ a)-[/(_ (ex_intro _ G' aG))-[P' PP'] _]. *)
  (*       apply: lt_next; [apply: PP'| apply: Ch]; last (by apply: tG'). *)
  (*       by apply: (g_stproj H aG). *)
  (*   - move: tr G P H; cofix Ch; move=> tr G P H; case: tr. *)
  (*     + move=> H1; elim/llts_inv: H1=>// _ _ Eq; move: Eq H=><-/=. *)
  (*       by move=>/qproj_end->; apply: eg_end. *)
  (*     + move=> a t; elim/llts_inv=>// _ a' t' P0 P' aP tP' [aa' tt' _ {P0}]. *)
  (*       move: aa' aP=>->aP {a'}. *)
  (*       move: tt' tP'=>->tP' {t'}. *)
  (*       move: (g_stequiv H) => /(_ a)-[_ /(_ (ex_intro _ P' aP))-[G' GG']]. *)
  (*       apply: eg_trans; [apply: GG'| apply: Ch]; last (by apply: tP'). *)
  (*       by apply: (g_stproj H GG'). *)
  (* Qed. *)
  Admitted.
   *)

  Fail Lemma rgparts_init G :
    rg_parts (init G) = participants G.
  (*
  Proof.
    elim/gty_ind2: G=>/=//.
    + by move=> [[p q] ty] G/=->.
    + move=> [[p q] ty] Gs /=/forall_member-Ih; do ! (congr cons).
      congr seq.flatten; rewrite -map_comp/comp/=.
      by apply/Fa_map_eq/forall_member => lG /(Ih lG).
  Qed.
   *)

  Fail Lemma msg_project_init G p :
    msg_proj (init G) p = Some [::].
  (*
  Proof.
    elim/gty_ind2: G=>// pr K Ih/=; rewrite -map_comp/comp/=.
    move: Ih; case: K=>[//|[l G] K/= [->]/=].
    by elim: K=>[//|[l1 G1] K/= Ih [-> /Ih->]].
  Qed.
   *)

  Fail Lemma rg_project_init G p :
    rg_proj (init G) p = project G p.
  (*
  Proof.
    elim/gty_ind2: G=>///=.
    - by move=>G->.
    - by move=>pr G ->.
    - move=>pr K /forall_member-Ih; rewrite -map_comp/comp/=; congr project_brn.
      by apply/Fa_map_eq/forall_member => x xK; move: (Ih x xK)=>->.
  Qed.
   *)

  Fail Lemma gvalid_isvalid G :
    is_valid (init G) = g_valid G.
  (*
  Admitted.
   *)

  Fail Lemma project_init G P :
    projection G == Some P -> q_projection (init G) = Some ([::], P).
  (*
  Proof.
    rewrite /projection/q_projection rgparts_init gvalid_isvalid.
    case: (g_valid G) =>//; elim: (participants G) P.
    - by move=>P /eqP-[<-].
    - move=> a ps Ih/= P.
      rewrite /q_proj msg_project_init rg_project_init option_comm.
      case: (project G a)=>// L.
      by move: Ih; case: (project_all G ps) =>// K /(_ K (eq_refl _))-> /eqP-[->].
  Qed.
   *)

  Fail Theorem global_local_trequiv G :
    forall P,
    projection G == Some P ->
    trace_equiv (init G) ([::], P).
  (*
  Proof. by move=>P /project_init/eqP; apply g_trequiv. Qed.
   *)


End TraceEquiv.

(* Validity of global types without participants missing, plus related lemmas
 * We need that, if valid G and step a G G', then valid G'

Print Assumptions global_local_trequiv.
 *)
