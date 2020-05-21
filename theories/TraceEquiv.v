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
Require Import MPST.QProjection.

Section TraceEquiv.

(*Finite set to be thought of as the set of all
participants involved in the protocol.

MAYBE USELESS

*)
Variable PAR : {fset role}.

Definition PAR2 := (PAR `*` PAR)%fset.







Open Scope fmap.


(*
Axiom IProj_end :
forall p G, ~ iPart_of p G -> (forall L, IProj p G L -> L = rl_end).
*)

(*
maybe the (p \in PAR) condition can be removed
*)
  Definition eProject (G: ig_ty) (E : {fmap role -> rl_ty}) : Prop :=
  (forall p, iPart_of p G -> p \in PAR) /\
  (forall p, p \in PAR ->
      (exists L,  IProj p G L /\ E.[? p] = Some L)).




(*again lemmas to be moved elsewhere later*)


  Lemma step_send_inv_aux F T C L Ty aa GG:
    step aa GG (ig_msg (Some L) F T C) ->
    aa = mk_act l_send F T L Ty -> GG = ig_msg None F T C ->
    exists G, C L = Some (Ty, G).
  Proof.
  elim/step_ind => //=.
  + move=> L0 F0 T0 C0 Ty0 G eqC => [] [].
    move=> H0 H1 H2 H3 =>[] []. elim; elim; move=> H4.
    by exists G; rewrite -H2 -H3 -H4.
  + move=> a l F0 T0 C0 C1 sub1 sub2 ne samed rall hp eqa => [] [].
    move=> eq1 eq2 eq3; move: sub1; rewrite eqa eq1 //=.
    by rewrite -(rwP negP) //=.
  Qed.

  Lemma step_send_inv F T C L Ty:
    step (mk_act l_send F T L Ty) (ig_msg None F T C) (ig_msg (Some L) F T C) ->
    exists G, C L = Some (Ty, G).
  Proof.
  by move=> hp; apply: (step_send_inv_aux hp).
  Qed.

(* the following is kind of true if... Q is empty...
at the moment it is only morally!


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
*)

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

  Lemma cProj_send_inv_aux F T C GG lT:
    Project F GG lT -> GG = (rg_msg F T C) ->
    F != T /\ (exists lC, lT = rl_msg l_send T lC /\
    same_dom C lC /\ R_all (upaco2 (Proj_ F) bot2) C lC).
  Proof.
  move=> hp; punfold hp; [move: hp => [] //=| by apply Proj_monotone].
  + move=> q gC lC neq samedom rall [eq1 eq2].
    by rewrite -eq1 -eq2; split; [| exists lC;  split; [ |]].
  + move=> q gC lC neq samedom rall [eq1 eq2 eq3].
    by move: neq; rewrite eq1 -(rwP negP).
  + move=> q s gC lC L neq1 neq2 neq3 samedom rall mer [eq1 eq2 eq3].
    by move: neq2; rewrite eq1 -(rwP negP).
  Qed.

  Lemma cProj_send_inv F T C lT:
    Project F (rg_msg F T C) lT ->
    F != T /\ (exists lC, lT = rl_msg l_send T lC /\
    same_dom C lC /\ R_all (upaco2 (Proj_ F) bot2) C lC).
  Proof.
  by move=> hp; apply: (cProj_send_inv_aux hp).
  Qed.


  Lemma cProj_recv_inv_aux F T C GG lT:
    Project T GG lT -> GG = (rg_msg F T C) ->
    F != T /\ (exists lC, lT = rl_msg l_recv F lC /\
    same_dom C lC /\ R_all (upaco2 (Proj_ T) bot2) C lC).
  Proof.
  move=> hp; punfold hp; [move: hp => [] //=| by apply Proj_monotone].
  + move=> q gC lC neq samedom rall [eq1 eq2 eq3].
    by move: neq; rewrite eq2 -(rwP negP).
  + move=> q gC lC neq samedom rall [eq1 eq2].
    by rewrite -eq1 -eq2; split; [rewrite eq_sym| exists lC; split; [ | split; [|]]].
  + move=> q s gC lC L neq1 neq2 neq3 samedom rall mer [eq1 eq2 eq3].
    by move: neq3; rewrite eq2 -(rwP negP).
  Qed.

  Lemma cProj_recv_inv F T C lT:
    Project T (rg_msg F T C) lT ->
    F != T /\ (exists lC, lT = rl_msg l_recv F lC /\
    same_dom C lC /\ R_all (upaco2 (Proj_ T) bot2) C lC).
  Proof.
  by move=> hp; apply: (cProj_recv_inv_aux hp).
  Qed.


  Lemma cProj_mrg_inv_aux p F T C GG lT:
    Project p GG lT ->
    p != F -> p != T -> GG = rg_msg F T C ->
    F != T /\ (exists lC, same_dom C lC /\
      R_all (upaco2 (Proj_ p) bot2) C lC /\
      Merge lC lT).
  Proof.
  move=> hp; punfold hp; [move: hp => [] //=| by apply Proj_monotone].
  + move=> q gC lC neq samedom rall neqF neqT [eq1 eq2 eq3].
    by move: neqF; rewrite eq1 -(rwP negP).
  + move=> q gC lC neq samedom rall neqF neqT [eq1 eq2 eq3].
    by move: neqT; rewrite eq2 -(rwP negP).
  + move=> q s gC lC lT0 neq1 neq2 neq3 samedom rall mer neqF neqT [eq1 eq2 eq3].
    split; [by move: neq1; rewrite eq1 eq2|exists lC].
    by rewrite -eq3; split; [ |split; [|]].
  Qed.

  Lemma cProj_mrg_inv p F T C lT:
    Project p (rg_msg F T C) lT ->
    p != F -> p != T ->
    F != T /\ (exists lC, same_dom C lC /\
      R_all (upaco2 (Proj_ p) bot2) C lC /\
      Merge lC lT).
  Proof.
  by move=> hp neq1 neq2; apply: (cProj_mrg_inv_aux hp neq1 neq2).
  Qed.


  Lemma IProj_end_inv_aux p GG CG CL:
    IProj p GG CL -> GG = ig_end CG ->
    Project p CG CL.
  Proof.
  by case=>//; move=> CG0 CL0 ipro [CGeq]; rewrite -CGeq.
  Qed.

  Lemma IProj_end_inv p CG CL:
    IProj p (ig_end CG) CL -> Project p CG CL.
  Proof.
  by move=> hp; apply (IProj_end_inv_aux hp).
  Qed.

  Lemma IProj_send1_inv_aux F T C GG CL:
    IProj F GG CL -> GG = (ig_msg None F T C) ->
    F != T /\ (exists lC, CL = rl_msg l_send T lC /\
    same_dom C lC /\ R_all (IProj F) C lC).
  Proof.
  case=>//.
  + move=> q gC lC neq samedom rall [eq1 eq2].
    by rewrite -eq1 -eq2; split; [| exists lC;  split; [ |]].
  + move=> o q gC lC neq samedom rall [eq1 eq2 eq3 eq4].
    by move: neq; rewrite eq2 -(rwP negP).
  + move=> q s gC lC L neq1 neq2 neq3 samedom rall mer [eq1 eq2 eq3].
    by move: neq2; rewrite eq1 eq_refl.
  Qed.

  Lemma IProj_send1_inv F T C CL:
    IProj F (ig_msg None F T C) CL ->
    F != T /\ (exists lC, CL = rl_msg l_send T lC /\
    same_dom C lC /\ R_all (IProj F) C lC).
  Proof.
  by move=> hp; apply: (IProj_send1_inv_aux hp).
  Qed.


  Lemma IProj_send2_inv_aux L p F T C GG CL:
    IProj p GG CL -> GG = (ig_msg (Some L) F T C) -> p != T ->
    F != T /\ (exists lC Ty, lC L = Some (Ty, CL) /\
    same_dom C lC /\ R_all (IProj p) C lC).
  Proof.
  case=>//.
  + move=> l Ty q r gC lC CL0 neq1 neq2 samedom rall Cleq [<-<-<-<-] neq3.
    by split=>//; exists lC, Ty; split.
  + move=> o q gC lC neq samedom rall [_ <-<-<-] {o F T C}.
    by rewrite eq_refl.
  Qed.

  Lemma IProj_send2_inv L p F T C CL:
    IProj p (ig_msg (Some L) F T C) CL -> p != T ->
    F != T /\ (exists lC Ty, lC L = Some (Ty, CL) /\
    same_dom C lC /\ R_all (IProj p) C lC).
  Proof.
  by move=> hp; apply: (IProj_send2_inv_aux hp).
  Qed.

 Lemma IProj_recv_inv_aux olb F T C GG CL:
    IProj T GG CL -> GG = (ig_msg olb F T C) ->
    F != T /\ (exists lC, CL = rl_msg l_recv F lC /\
    same_dom C lC /\ R_all (IProj T) C lC).
  Proof.
  case =>//.
  + move=> q gC lC neq samedom rall [eq1 eq2 eq3].
    by move: neq; rewrite eq3 -(rwP negP).
  + move=> l Ty q r cG cL L neq1 _ _ _ _ [_ _ eq1].
    by move: eq1 neq1=>->/eqP.
  + move=> o q gC lC neq samedom rall [eq1 eq2 eq3].
    by rewrite -eq2 -eq3; split; [rewrite eq_sym| exists lC; split; [ | split; [|]]].
  + move=> q s gC lC L neq1 neq2 neq3 samedom rall mer [eq1 eq2 eq3 eq4].
    by move: neq3; rewrite eq3 -(rwP negP).
  Qed.

  Lemma IProj_recv_inv olb F T C CL:
    IProj T (ig_msg olb F T C) CL ->
    F != T /\ (exists lC, CL = rl_msg l_recv F lC /\
    same_dom C lC /\ R_all (IProj T) C lC).
  Proof.
  by move=> hp; apply: (IProj_recv_inv_aux hp).
  Qed.

  Lemma IProj_mrg_inv_aux p F T C GG CL:
    IProj p GG CL ->
    p != F -> p != T -> GG = ig_msg None F T C ->
    F != T /\ (exists lC, same_dom C lC /\
      R_all (IProj p) C lC /\
      Merge lC CL).
  Proof.
  case =>//.
  + move=> q gC lC neq samedom rall neqF neqT [eq1 eq2 eq3].
    by move: neqF; rewrite eq1 -(rwP negP).
  + case=>// q cG cL neq samedom rall neqF neqT [eq1 eq2 eq3].
    by move: neqT; rewrite eq2 -(rwP negP).
  + move=>q s gC lC CL0 neq1 neq2 neq3 samedom rall mer neqF neqT [eq1 eq2 eq3].
    split; [by move: neq1; rewrite eq1 eq2|exists lC].
    by rewrite -eq3; split; [ |split; [|]].
  Qed.

  Lemma IProj_mrg_inv p F T C CL:
    IProj p (ig_msg None F T C) CL ->
    p != F -> p != T ->
    F != T /\ (exists lC, same_dom C lC /\
      R_all (IProj p) C lC /\
      Merge lC CL).
  Proof.
  by move=> hp neq1 neq2; apply: (IProj_mrg_inv_aux hp neq1 neq2).
  Qed.

  Lemma eProject_send_none F T C E:
    eProject (ig_msg None F T C) E ->
    F != T /\ (exists lC, E.[? F]%fmap = Some (rl_msg l_send T lC) /\
    same_dom C lC /\ R_all (IProj F) C lC).
  Proof.
  elim=> parPAR hp.
  move: (hp _ (parPAR _ (ipof_from None F T C))); elim=> lT.
  elim=> pro eq; move: (IProj_send1_inv pro).
  elim=> neq; elim=> lC; elim=> lTeq; elim=> samedom rall.
  split; [by []|exists lC].
  split; [by rewrite eq; apply f_equal| split; [ by []|]].
  move: rall; rewrite /R_all; move=> rall L Ty G lTT someg somel.
  by apply: (rall _ _ _ _ someg somel).
  Qed.


  (* Lemma eProject_send_some L F T C E: *)
  (*   eProject (ig_msg (Some L) F T C) E -> *)
  (*   F != T /\ (exists lC Ty lT, lC L = Some (Ty, lT) /\ *)
  (*   E.[? F]%fmap = Some lT /\ same_dom C lC /\ R_all (IProj F) C lC). *)
  (* Proof. *)
  (* elim=> parPAR hp. *)
  (* move: (hp _ (parPAR _ (ipof_from (Some L) F T C))); elim=> lT. *)
  (* elim=> pro eq; move: (IProj_send2_inv pro). *)
  (* elim=> neq; elim=> lC; elim=> Ty; elim=> lCLeq. *)
  (* elim=> samedom rall; split; [by []|exists lC, Ty, lT]. *)
  (* split; [by []| split; [ by []|split; [by []|]]]. *)
  (* move: rall; rewrite /R_all; move=> rall L0 Ty0 G lTT someg somel. *)
  (* by apply: (rall _ _ _ _ someg somel). *)
  (* Qed. *)



  Lemma eProject_recv o F T C E:
    (*T \in PAR ->*) eProject (ig_msg o F T C) E ->
    F != T /\ (exists lC, E.[? T]%fmap = Some (rl_msg l_recv F lC) /\
    same_dom C lC /\ R_all (IProj T) C lC).
  Proof.
  elim=> parPAR hp.
  move: (hp _ (parPAR _ (ipof_to o F T C))); elim=> lT.
  elim=> pro eq; move: (IProj_recv_inv pro).
  elim=> neq; elim=> lC; elim=> lTeq.
  elim=> samedom rall; split; [by []|exists lC].
  split; [by rewrite -lTeq | split; [ by []|]].
  move: rall; rewrite /R_all; move=> rall L0 Ty0 G lTT someg somel.
  by apply: (rall _ _ _ _ someg somel).
  Qed.


(*to be moved in Local.v*)


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


  Lemma EqL_l_msg_inv_aux lT lT' a p C:
    EqL lT lT' -> lT = rl_msg a p C ->
    exists C', same_dom C C' /\
       R_all EqL C C' /\ lT' = rl_msg a p C'.
  Proof.
  move=> hp; punfold hp; move: hp => [] //=.
  move=> a0 p0 C1 C2 samed rall [eq1 eq2 eq3].
  exists C2; rewrite eq1 eq2 -eq3; split; [|split] => //=.
  rewrite /R_all; move=> L Ty lT1 lT2 ceq1 ceq2.
  rewrite /R_all in rall; move: (rall L Ty lT1 lT2 ceq1 ceq2).
  by rewrite /upaco2; elim; rewrite //=.
  Qed.

  Lemma EqL_l_msg_inv a p C lT':
    EqL (rl_msg a p C) lT' ->
    exists C', same_dom C C' /\
       R_all EqL C C' /\ lT' = rl_msg a p C'.
  Proof.
  by move=> hp; apply: (EqL_l_msg_inv_aux hp).
  Qed.




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

(*next two admitted lemmas should have similar proofs
actually they should be doubled*)

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
    move=> (*op*) F T CONT; case: (@eqP _ p F).
    * move=> pF; rewrite pF.
      - move=> hpro; move: (cProj_send_inv hpro); elim=> neq.
        elim=> lC0; elim; move=> [eq1 eq2 eq3]; elim=> samed0 ral.
        apply /paco2_fold; rewrite eq1 eq2.
        apply (prj_send neq).
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
        rewrite eq1 eq2; apply: (prj_recv neqFT).
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
        apply: (@prj_mrg _ _ _ _ _
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



  Lemma EqL_IProj p G lT lT':
    IProj p G lT -> EqL lT lT' -> IProj p G lT'.
  Proof.
  move=> hp; move: hp lT'; elim.
  + move=> CG {}lT Pro lT' eqL; apply: iprj_end.
    by apply: (EqL_Project eqL Pro).
  + move=> q C lC neq samed rall Ih lT' eqL.
    move: (EqL_l_msg_inv eqL); elim=> lC'; elim=> samedom.
    elim=> rall' ->; apply: (iprj_send1 neq).
    * by move=> L Ty; rewrite (samed L Ty).
    * move=> L Ty G0 lT0' CL lCL'.
      move: (samedom L Ty); elim=> _.
      elim; [move=> lT0 lCL | by exists lT0'].
      apply: (Ih _ _ _ _ CL lCL).
      by apply: (rall' _ _ _ _ lCL lCL').
  + move=> L Ty q r C lC lT0 neq1 neq2 samed rall Ih lCL lT0' eqL.
    move:(samed L Ty);elim=> _;elim;[move=> G0 CL|by exists lT0].
    apply: (@iprj_send2 p L Ty q r C (extend L (Ty, lT0') lC) _ neq1 neq2).
    * apply: (same_dom_extend_some_l _ samed CL).
    * move=> LL TTy GG lTT CLL; rewrite /extend; case: ifP.
      - rewrite -(rwP eqP); move=> eqLL [eqTy eqlT0'].
        rewrite -eqlT0'; rewrite -eqLL in CLL.
        move: CLL; rewrite CL; move=> [_ eqG0]; rewrite -eqG0.
        by apply: (Ih _ _ _ _ CL lCL).
      - by move=> neqLL lCLL; apply: rall CLL lCLL.
    * by rewrite /extend; case: ifP =>//; rewrite eq_refl //.
  + move=> o q C lC neq samed rall Ih lT' eqL.
    move: (EqL_l_msg_inv eqL); elim=> lC'; elim=> samedom.
    elim=> rall' ->; apply: (iprj_recv o neq).
    * by move=> L Ty; rewrite (samed L Ty).
    * move=> L Ty G0 lT0' CL lCL'.
      move: (samedom L Ty); elim=> _.
      elim; [move=> lT0 lCL | by exists lT0'].
      apply: (Ih _ _ _ _ CL lCL).
      by apply: (rall' _ _ _ _ lCL lCL').
  + move=> q s C lC lT0 neqqs neqpq neqps samed rall Ih mer lT' eqL.
    apply: (@iprj_mrg _ _ _ _
          (same_dom_const C lT') _ neqqs neqpq neqps).
    * by apply: same_dom_const_same_dom.
    * move=> L Ty G0 lTT' CL sdLa.
      move: (same_dom_const_some sdLa)=>->.
      move: (samed L Ty); elim=> sam _; move: sam.
      elim; [move=> lTT lCL | by exists G0].
      by apply: (Ih _ _ _ _ CL lCL) (EqL_trans (mer _ _ _ lCL) eqL).
    * move=> Ln Tn lTn sdc; move: (same_dom_const_some sdc) =>-> //=.
  Qed.



  Lemma iPart_of_end_unr p CG:
    iPart_of p (ig_end CG) <-> iPart_of p (rg_unr CG).
  Proof.
  split.
  + case E: _ / =>[{}p cG P_OF|||]//; move: E=>[->] {CG}.
    case: P_OF =>[F T C||]/=; try by constructor.
    move=>{}p F T C L G Ty C_L part_G; set C' := fun L=>_.
    have C_L': C' L = Some (Ty, ig_end G) by rewrite /C' C_L.
    by apply/(ipof_cont None F T C_L')/ipof_end/part_G.
  + case: CG=>//= F T C.
    set C' := fun lbl=>_.
    case E: _ /
      =>[ //
        | O F' T' C0
        | O F' T' C0
        | {}p O F' T' C0 {}L G Ty C0_L part_G
        ]; constructor.
    + by move: E=>[_ <- _ _]; constructor.
    + by move: E=>[_ _ <- _]; constructor.
    + move: E C0_L=>[_ _ _ <-] C_L {F' T' C0 O}.
      move: C_L; rewrite /C'; case C_L: (C L)=>[[{}Ty cG]|//] [_ cG_G].
      move: cG_G part_G=><-; case E: _ / =>[{}p cG' part_CG|||]//.
      move: E part_CG=>[<-] part_CG {cG'}.
      by apply/(pof_cont F T C_L)/part_CG.
  Qed.
(* I need some inversion lemmas
*
* Update 28/04/2020, DC comment: Fixed. True, you can try and see how to add
* inversion lemmas. However, I think it is generally easier to use [case E: _ /
* H]. I Recommend to check how it works. It can be confusing (I still do not
* understand it fully, but ...). Another approach is using [Deriving Scheme]
* for deriving an inversion scheme, and using [elim/...]. This saves loads of
* time proving inversion lemmas
*)

  Lemma step_subject_iPart_of a G G':
    step a G G' -> ig_wfcont G -> iPart_of (subject a) G.
  Proof.
  elim.
  + move=> L F T C Ty G0 CL wf; rewrite /subject.
    by apply ipof_from.
  + move=> L F T C Ty G0 CL wf; rewrite /subject.
    by apply ipof_to.
  + move=> a0 l F T C0 C1 nF nT ne sd ra ih wf.
    move: (ig_wfcont_msg_inv wf); elim=> neqFT.
    elim; elim=> L; elim=> Ty; elim=> G0.
    elim=> C0L wf0 wfall0; apply: (ipof_cont _ _ _ C0L).
    have G1_aux: exists G1, C1 L = Some (Ty, G1).
      by rewrite /same_dom in sd; apply sd; exists G0.
    move: G1_aux; elim=> G1 C1L.
    by apply (ih _ _ _ _ C0L C1L).
  + move=> a0 L F T C0 C1 nT sd ron ronpof wf.
    case: (@eqP _ (subject a0) F).
    - by move => sa0F; rewrite sa0F; apply ipof_from.
    - rewrite (rwP eqP) (rwP negP); move=> sa0F.
      move: (ig_wfcont_msg_inv wf); elim=> neq; elim.
      elim=> L0; elim=> Ty; elim=> G0; elim=> C0L wf0 wfall0.
      rewrite /R_only in ronpof; move: ronpof; elim=> hp.
      elim=> Ty0; elim=> G0'; elim=> G1'; elim=> C0L'.
      elim=> C1L' ih0; apply: (ipof_cont  _ _ _ C0L').
      move: ih0; elim=> st ih; apply ih, (wfall0 _ _ _ C0L').
  + move=> a0 CG G0 st ih wf; apply ipof_end.
    move: (ih (ig_wfcont_rg_unr wf)).
    move=>/iPart_of_end_unr; move: (subject a0) => p.
    by case E: _ / =>[{}p cG part_CG|||]//; move: E=>[->].
  Qed.



  Open Scope mpst_scope.
  Open Scope fset.

  Lemma all_fmap
    (K : choiceType) (FS: {fset K}) (U : Type) (R: K -> (option U) -> Prop):
    (forall x, exists u : (option U), x \in FS -> R x u)
      -> exists f: {fmap K -> U}, forall x, x \in FS -> R x (f.[? x]).
  Proof.
  elim /finSet_rect: FS=> X; case: (@eqP _ X fset0 ).
  + by move=>-> IH hp; exists [fmap].
  + rewrite (rwP eqP) (rwP negP) -(rwP (fset0Pn X)).
    elim=> x xin IH build; move: (IH _ (fproperD1 xin)) => IH0.
    have forIH0: forall x0 : K, exists u : option U, x0 \in X `\ x -> R x0 u.
      move=> x0; move: (build x0); elim=> u0 impl.
      exists u0; move=> hp; apply: impl; rewrite in_fsetD in hp.
      by move: hp; rewrite -(rwP andP); elim.
    move: (IH0 forIH0); elim=> f' hpf'.
    move: (build x); elim=> u hpu'; move: (hpu' xin); move=> hpu.
    case E: u => [uu |].
    - exists (f'.[x <- uu]); move=> y; rewrite fnd_set.
      case: ifP; [by rewrite -(rwP eqP) -E; move =>->|].
      move=> neq yin; apply hpf'; rewrite in_fsetD.
      rewrite -(rwP andP); split=>//.
      rewrite -(rwP negP) -(rwP (fset1P y x)) //.
      by rewrite (rwP eqP) (rwP negP); move: (negbT neq).
    - exists (f'.[~x]); move=> y; rewrite fnd_rem1.
      case: ifP.
      * move=> neq yinX; apply hpf'; rewrite in_fsetD.
        rewrite -(rwP andP); split =>//.
        rewrite -(rwP negP) -(rwP (fset1P y x)).
        by rewrite (rwP eqP) (rwP negP).
      * move=> neq; move: (negbT neq).
        move=> {}neq; move: (negbNE neq).
        rewrite -(rwP eqP); move =>-> _.
        by rewrite E in hpu.
  Qed.


  Lemma exists_rel_finset_inhabited
    (K : choiceType) (FS: {fset K}) (x : K)
    (U : Type) (uu : U)
    (R: K -> U -> Prop):
    (x \in FS -> exists u, R x u)
    ->
    (exists u, x \in FS -> R x u).
  Proof.
  case xin: (x \in FS) =>//=.
  + by elim =>//= u Rxu; exists u.
  + by move=> _; exists uu.
  Qed.




  Lemma inPAR_msg_cont o F T C L Ty G:
    (forall p, iPart_of p (ig_msg o F T C) -> p \in PAR)
    -> C L = Some (Ty, G)
    -> (forall p, iPart_of p G -> p \in PAR).
  Proof.
  move=> msginPAR CL p part.
  apply: (msginPAR _ (ipof_cont o F T CL part)).
  Qed.


(*   Lemma eProject_cont_build o F T C E L Ty G: *)
(*     eProject (ig_msg o F T C) E -> C L = Some (Ty, G) *)
(*     -> forall p, p \in PAR -> *)
(*     (exists L0 : rl_ty, IProj p G L0). *)
(*   Proof. *)
(*   elim=> allinPAR epro CL p inPAR. *)
(*   move: (epro  _ inPAR). *)
(*   elim=> lT;  case: (@eqP _ p F). *)
(*   + move =>->; case eq: o=> [L0|]. *)
(*     * elim=> {}ipro _; move: (IProj_send2_inv ipro); elim=> neq. *)
(*       elim=> lC; elim=> Ty0; elim=> _; elim=> samedom rall. *)
(*       move: (samedom L Ty); elim; elim; [|by exists G]. *)
(*       move=> lT0 lCL _; exists lT0; by apply: (rall L Ty). *)
(*     * elim=> {}ipro _; move: (IProj_send1_inv ipro); elim=> neq. *)
(*       elim=> lC; elim=> _; elim=> samedom rall. *)
(*       move: (samedom L Ty); elim; elim; [|by exists G]. *)
(*       move=> lT0 lCL _; exists lT0; by apply: (rall L Ty). *)
(*   + rewrite (rwP eqP) (rwP negP); move=> neqpF. *)
(*     case: (@eqP _ p T). *)
(*     * move=> eqpT; rewrite eqpT. *)
(*       elim=> {}ipro _; move: (IProj_recv_inv ipro). *)
(*       elim=> neq; elim=> lC; elim=> _; elim=> samedom rall. *)
(*       move: (samedom L Ty); elim; elim; [|by exists G]. *)
(*       move=> lT0 lCL _; exists lT0; by apply: (rall L Ty). *)
(*     * rewrite (rwP eqP) (rwP negP); move=> neqpT. *)
(*       elim=> {}ipro _; move: (IProj_mrg_inv ipro neqpF neqpT). *)
(*       elim=> neq; elim=> lC; elim=> samedom; elim=> rall mrg. *)
(*       move: (samedom L Ty); elim; elim; [|by exists G]. *)
(*       move=> lT0 lCL _; exists lT0; by apply: (rall L Ty). *)
(*   Qed. *)


(* Lemma eProject_cont o F T C E L Ty G (lC : lbl /-> mty * rl_ty): *)
(*   eProject (ig_msg o F T C) E -> C L = Some (Ty, G) *)
(*   -> exists E0, eProject G E0. *)
(* (*{E0 : role -> (option rl_ty)| *)
(*     forall p : role, *)
(*     iPart_of p G -> exists L : rl_ty, IProj p G L /\ E0 p = Some L}.*) *)
(* Proof. *)
(*   move=> epro CL. *)
(*   move: epro (eProject_cont_build epro CL). *)
(*   elim=> allinPAR {}epro build''. *)
(*   have build': forall p : role, exists L0 : rl_ty, p \in PAR -> IProj p G L0. *)
(*     move=> p; move: (build'' p); move=> {}build''. *)
(*     apply: (@exists_rel_finset_inhabited *)
(*         _ _ _ _ rl_end (fun p L => IProj p G L) build''). *)
(*   have build: forall p : role, exists oL0 : (option rl_ty), p \in PAR *)
(*     -> exists L0, (IProj p G L0 /\ oL0 = Some L0). *)
(*     move=> p; move: ( build' p); elim=> L0 hp. *)
(*     apply: (@exists_rel_finset_inhabited _ PAR p _ None *)
(*       (fun p oL => exists L1 : rl_ty, IProj p G L1 /\ oL = Some L1) *)
(*       ). *)
(*     move=> pinPAR; exists (Some L0), L0; split =>//=. *)
(*     by apply hp. *)
(*   move: (all_fmap build). *)
(*   elim=> E0 hp; exists E0; split=>//=. *)
(*   by apply: (inPAR_msg_cont allinPAR CL). *)
(*   Qed. *)


  Lemma iproj_send1_exists p q KsG:
      p != q ->
      (exists KsL, same_dom KsG KsL /\ R_all (IProj p) KsG KsL) ->
      exists lT, IProj p (ig_msg None p q KsG) lT. (*rl_msg l_send q KsL*)
  Proof.
  move=> neq; elim=> KsL; elim=> sd rall.
  by exists (rl_msg l_send q KsL); apply: iprj_send1.
  Qed.


(*  Lemma gstep_doact_send a G G' p q lbl tyy E:
    step a G G' -> a = (a_send p q lbl tyy) -> eProject G E ->
    ig_wfcont G -> well_formed G ->
    exists E', do_act E l_send p q lbl tyy = Some E'.
  Proof.
  move=> stephp; elim/step_ind: stephp E =>//=.
  + admit.
  + move=> a0 F T C0 C1 nF nT sd ra IH aeq E epro wfc wf.
  Admitted.*)


(*playing with continuations*)
  Inductive cont_of: (lbl /-> mty * rg_ty) -> rg_ty -> Prop :=
    | cof_0 C F T: cont_of C (rg_msg F T C)
    | cof_rec C F T CC L G Ty: CC L = Some (Ty, G)
      -> cont_of C G -> cont_of C (rg_msg F T CC).

  Inductive iCont_of: (lbl /-> mty * ig_ty) -> ig_ty -> Prop :=
    | icof_end C cG: cont_of C cG -> iCont_of
      (fun lbl =>  match C lbl with
                    | None => None
                    | Some (t, G) => Some (t, ig_end G)
                    end) (ig_end cG)
    | icof_0 C o F T: iCont_of C (ig_msg o F T C)
    | icof_rec C o F T CC L G Ty: CC L = Some (Ty, G)
      -> iCont_of C G -> iCont_of C (ig_msg o F T CC).

  Definition findom_cont G (LAB : {fset lbl}) : Prop :=
  (forall C, iCont_of C G ->
    (forall L ty GG, C L = Some (ty, GG) -> L \in LAB) ).

  Lemma all_fset_option_map
    (K : choiceType) (FS: {fset K}) (U : Type) (R: K -> (option U) -> Prop):
    (forall x, exists u : (option U), x \in FS -> R x u)
      -> exists (f: K -> option U), forall x, x \in FS -> R x (f x).
  Proof.
  elim /finSet_rect: FS => X; case: (@eqP _ X fset0).
  + move=>-> ih build; exists (fun x=> None).
    by move=> x.
  + rewrite (rwP eqP) (rwP negP) -(rwP (fset0Pn X)).
    elim=> x xin IH build; move: (IH _ (fproperD1 xin)) => IH0.
    have forIH0: forall x0 : K, exists u : option U, x0 \in X `\ x -> R x0 u.
      move=> x0; move: (build x0); elim=> u0 impl.
      exists u0; move=> hp; apply: impl; rewrite in_fsetD in hp.
      by move: hp; rewrite -(rwP andP); elim.
    move: (IH0 forIH0); elim=> f' hpf'.
    move: (build x); elim=> u hpu'; move: (hpu' xin); move=> hpu.
    exists (fun y => if y == x then u else f' y).
    move=> x0; case: ifP.
    * by rewrite -(rwP eqP); move=>->.
    * move=> neq; rewrite -(fsetD1K xin).
      rewrite -(rwP (fsetUP x0 [fset x] (X`\ x))).
      by elim; [rewrite -(rwP (fset1P x0 x)) (rwP eqP) neq | apply: hpf'].
  Qed.



  Lemma forallforallforall (T: Type) (P Q: T -> Prop):
  (forall (x: T), P x) /\ (forall (x: T), Q x)
  -> (forall x, P x /\ Q x).
  Proof.
  by elim=> PP QQ x; split; [apply PP|apply QQ].
  Qed.

  Definition Projection G P := eProject G P.1 /\ qProject G P.2.

  Lemma eProj_igend_from F T C E :
    eProject (ig_end (rg_msg F T C)) E ->
    exists L : rl_ty, IProj F (ig_end (rg_msg F T C)) L /\ E.[? F] = Some L.
  Proof. by move=>[/(_ F (ipof_end (pof_from _ _ _)))-H /(_ F H)]. Qed.

  Lemma eProj_igend_to F T C E :
    eProject (ig_end (rg_msg F T C)) E ->
    exists L : rl_ty, IProj T (ig_end (rg_msg F T C)) L /\ E.[? T] = Some L.
  Proof. by move=>[/(_ T (ipof_end (pof_to _ _ _)))-H /(_ T H)]. Qed.

  Lemma eProj_igmsg_from o F T C E :
    eProject (ig_msg o F T C) E ->
    exists L : rl_ty, IProj F (ig_msg o F T C) L /\ E.[? F] = Some L.
  Proof. by move=>[/(_ F (ipof_from _ _ _ _))-H /(_ F H)]. Qed.

  Lemma eProj_igmsg_to o F T C E :
    eProject (ig_msg o F T C) E ->
    exists L : rl_ty, IProj T (ig_msg o F T C) L /\ E.[? T] = Some L.
  Proof. by move=>[/(_ T (ipof_to _ _ _ _))-H /(_ T H)]. Qed.

  Lemma eProj_part p G E :
      eProject G E -> iPart_of p G -> exists L, IProj p G L /\ E.[? p] = Some L.
  Proof.
  by elim=> inPAR epro part; apply: epro; apply: inPAR.
  Qed.

  Lemma step_cont_ipart A G G' :
    step A G G' ->
    iPart_of (subject A) G.
  Proof.
    elim=> {A G G'}
    [ l F T C Ty G H
    | l F T C Ty G H
    | A l F T C0 C1 a_F a_T [Ty [G E]] DOM ST Ih
    | A l F T C0 C1 a_T DOM ST [_ [Ty [G [G' [E [E' [ST' Ih]]]]]]]
    | A CG G ST Ih
    ].
    + by apply: ipof_from.
    + by apply: ipof_to.
    + apply: ipof_cont; first by apply: E.
      move: (DOM l Ty)=>[/(_ (ex_intro _ _ E))-[G' C1_L] _].
      by apply: (Ih l Ty G G' E C1_L).
    + apply: ipof_cont; first by apply: E.
      apply: Ih.
    + by apply/iPart_of_end_unr.
  Qed.

  Lemma iPart_of_inv p o F T C :
    iPart_of p (ig_msg o F T C) ->
    (p = F) \/ (p = T) \/ (exists l Ty G, C l = Some (Ty, G) /\ iPart_of p G).
  Proof.
    case EQ: _ / =>
    [ //
    | o' F' T' C'
    | o' F' T' C'
    | {}p o' F' T' C' l G Ty C'_L p_G
    ]; [left|right;left|right;right].
    + by move: EQ=>[_ <- _].
    + by move: EQ=>[_ _ <-].
    + move: EQ C'_L=>[_ _ _ <-] C_L.
      by exists l, Ty, G; split.
  Qed.

  (* Definition prefix prf p E := *)
  (*   match E.[? p] with *)
  (*   | None => E *)
  (*   | Some L => E.[p <- rl_msg a ] *)

  Lemma doact_other p E A L :
    subject A != p -> match do_act E A with
                      | Some E' => Some E'.[p <- L]
                      | None => None
                      end = do_act E.[p <- L] A.
  Proof.
    case: A=>[a F T l Ty]; rewrite /do_act fnd_set => /=SUBJ.
    rewrite (negPf SUBJ).
    case: (E.[? F])=>[[//|a0 q C] |//].
    case: (C l)=>[[Ty' L']|//].
    case: ifP=>// _.
    by rewrite setfC eq_sym (negPf SUBJ).
  Qed.

  Lemma runnable_upd A E Q L p :
    subject A != p -> runnable A (E, Q) <-> runnable A (E.[p <- L], Q).
  Proof.
    move=> SUBJ; rewrite /runnable/= -doact_other//.
    by case: (do_act E A)=>[_|//].
  Qed.

  Definition run_act A E :=
    match do_act E A with
    | Some E' => E'
    | None => E
    end.

  Lemma eProj_Some_next l F T C E :
    eProject (ig_msg (Some l) F T C) E ->
    forall Ty G,
      C l = Some (Ty, G) ->
      eProject G (run_act (mk_act l_recv T F l Ty) E).
  Proof.
    rewrite /eProject=>[[P H]] Ty G Cl.
    move: (H _ (P _ (ipof_to _ _ _ _)))=>[L [PRJ ET]].
    move: PRJ=>/IProj_recv_inv=>[[FT [CL [L_msg [DOM PRJ]]]]].
    move: (DOM l Ty)=>[/(_ (ex_intro _ _ Cl))-[L' CLl] _].
    split; first by move=>p pG; apply/P/(ipof_cont _ _ _ Cl).
    move=> p; case: (boolP (p == T))=>[/eqP->|pF] pP.
    - exists L'; split; first by apply/(PRJ _ _ _ _ Cl CLl).
      by rewrite /run_act/= ET L_msg CLl !eq_refl /andb fnd_set eq_refl.
    - move: (H _ pP)=>[Lp [PRJ' Ep]].
      move: PRJ'=>/IProj_send2_inv/(_ pF)=>[[_ [lC [Ty0 [lCl [DOM' PRJ']]]]]].
      move: (DOM' l Ty)=>[/(_ (ex_intro _ _ Cl))-[Lp' lCl'] _].
      move: lCl'; rewrite lCl=>[[Eq_Ty0 Eq_Lp]].
      move: Eq_Ty0 Eq_Lp lCl=>-> _ lCl {Lp' Ty0}.
      exists Lp; split; first by apply: (PRJ' _ _ _ _ Cl lCl).
      by rewrite /run_act/= ET L_msg CLl !eq_refl /andb fnd_set (negPf pF).
  Qed.

  Lemma eProj_None_next F T C E :
    eProject (ig_msg None F T C) E ->
    forall l Ty G,
      C l = Some (Ty, G) ->
      eProject G (run_act (mk_act l_send F T l Ty)
                          (run_act (mk_act l_recv T F l Ty) E)).
  Proof.
    rewrite /eProject => [[P H]] l Ty G C_l.
    split; first by move=> p /(ipof_cont None F T C_l)/P.
    move: (H _ (P _ (ipof_from  _ _ _ _)))
      => [L'' [/IProj_send1_inv-[FT [lC [-> [DOM PRJ]]]] EF]].
    move: (DOM l Ty)=>[/(_ (ex_intro _ _ C_l))-[L lC_l] _].
    move: (H _ (P _ (ipof_to _ _ _ _)))
      => [L' [/IProj_recv_inv-[_ [lC' [-> [DOM' PRJ']]]] ET]].
    move: (DOM' l Ty)=>[/(_ (ex_intro _ _ C_l))-[L''' lC_l'] _].
    move=> p; case: (boolP (p == F)) =>[/eqP-> _|pF].
    - exists L; split; first by move: PRJ => /(_ _ _ _ _ C_l lC_l).
      rewrite /run_act/= ET lC_l' !eq_refl /andb fnd_set (negPf FT) EF lC_l.
      by rewrite !eq_refl fnd_set eq_refl.
    - case: (boolP (p == T)) =>[/eqP-> _|pT].
      + exists L'''; split; first by move: PRJ' => /(_ _ _ _ _ C_l lC_l').
        rewrite /run_act/= ET lC_l' !eq_refl /andb fnd_set (negPf FT) EF lC_l.
        by rewrite !eq_refl fnd_set eq_sym (negPf FT) fnd_set eq_refl.
      + move=>/H-[L4 [/IProj_mrg_inv/(_ pF)/(_ pT)
                      -[_ [lC'' [DOM'' [PRJ'' MRG]]]] Ep]].

        move: (DOM'' l Ty)=>[/(_ (ex_intro _ _ C_l))-[L5 lC_l''] _].
        move: (MRG _ _ _ lC_l'')=>EQ_L4.
        exists L4; split; first by apply/(EqL_IProj _ EQ_L4)/(PRJ'' _ _ _ _ C_l).
        rewrite /run_act/= ET lC_l' !eq_refl /andb fnd_set (negPf FT) EF lC_l.
        by rewrite !eq_refl !fnd_set (negPf pF) (negPf pT).
  Qed.

  Lemma runnable_next A A' E Q :
    subject A != subject A' -> runnable A (E, Q) <-> runnable A (run_act A' E, Q).
  Proof.
    rewrite /run_act/do_act; case: A'=>[a F T l Ty]/=.
    case: (E.[? F])=>[[//|a' p C]|//].
    case: (C l)=>[[Ty' L']|//].
    case: ifP=>[_|//].
    by apply: runnable_upd.
  Qed.

  Lemma runnable_next_deq A l p q Ty E Q Q' :
    subject A != q -> deq Q (p, q) == Some (l, Ty, Q') ->
    runnable A (E, Q) <-> runnable A (E, Q').
  Proof.
    move=> Aq; rewrite /deq.
    case: (Q.[? (p, q)])=>[[//|[l' Ty' [|a l0]]]|//]/=/eqP-[_ _ <-] {Q'}.
    + rewrite /runnable/=.
      case: (do_act E A)=>// _; case: A Aq=>//[[//|] q0 p0 l0 Ty0]/= qq0.
      rewrite /deq fnd_rem1 xpair_eqE negb_and orbC qq0 /orb.
      by case: (Q.[? (p0, q0)])=>[[|[l1 Ty1 [|]]]|].
    + rewrite /runnable/=.
      case: (do_act E A)=>// _; case: A Aq=>// [[//|] q0 p0 l1 Ty0]/= qq0.
      rewrite /deq fnd_set xpair_eqE (negPf qq0) andbC /andb.
      by case: (Q.[? (p0, q0)])=>[[|[l2 Ty1 [|]]]|].
  Qed.

  Lemma same_dom_sym A B (C1 : lbl /-> mty * A) (C2 : lbl /-> mty * B) :
    same_dom C1 C2 <-> same_dom C2 C1.
  Proof. by split=>H l Ty; move: (H l Ty)=>->. Qed.

  Lemma same_dom_trans A B C
        (C1 : lbl /-> mty * A) (C2 : lbl /-> mty * B) (C3 : lbl /-> mty * C) :
    same_dom C1 C2 -> same_dom C2 C3 -> same_dom C1 C3.
  Proof. by move=>H0 H1 l Ty; move: (H0 l Ty) (H1 l Ty)=>->. Qed.

  Lemma IProj_unr p CG L:
    IProj p (ig_end CG) L -> IProj p (rg_unr CG) L.
  Proof.
    move=>/IProj_end_inv; case: CG.
    + move=>PRJ; move: (cProj_end_inv PRJ)=>EQ.
      by move: EQ PRJ=>->PRJ; constructor.
    + move=>F T C /=; set CC := fun l=>_.
      have DOM_CC: same_dom C CC.
      { move=> l Ty; split; move=>[G E1];
          first (by exists (ig_end G); rewrite /CC E1).
        by move: E1; rewrite /CC; case: (C l)=>[[Ty' iG]|//] [->_]; exists iG.
      }
      case: (boolP (p == F))=>[/eqP->|pF]; [|case: (boolP (p == T))=>[/eqP->|pT]].
      - move=>/cProj_send_inv-[FT [Cl [-> [DOM PRJ]]]].
        constructor=>//; first by move=> l Ty; rewrite -DOM_CC.
        move=> L0 Ty G L' CC_L0 Cl_L0; move: CC_L0; rewrite /CC.
        move: (DOM L0 Ty)=>[_ /(_ (ex_intro _ _ Cl_L0))-[CG C_L0]].
        rewrite C_L0 =>[[<-]]; constructor.
        by move: PRJ; move=>/(_ L0 Ty CG L' C_L0 Cl_L0)=>[[PRJ|//]].
      - move=>/cProj_recv_inv-[FT [Cl [-> [DOM PRJ]]]].
        move: FT; rewrite eq_sym=>FT.
        constructor=>//; first by move=> l Ty; rewrite -DOM_CC.
        move=> L0 Ty G L' CC_L0 Cl_L0; move: CC_L0; rewrite /CC.
        move: (DOM L0 Ty)=>[_ /(_ (ex_intro _ _ Cl_L0))-[CG C_L0]].
        rewrite C_L0 =>[[<-]]; constructor.
        by move: PRJ; move=>/(_ L0 Ty CG L' C_L0 Cl_L0)=>[[PRJ|//]].
      - move=>/cProj_mrg_inv/(_ pF pT)-[FT [lC [DOM [PRJ MRG]]]].
        have /same_dom_trans/(_ DOM)-DOM_CC':
          same_dom CC C by move: DOM_CC=>/same_dom_sym.
        apply: iprj_mrg=>// l Ty G L' CC_l lC_l.
        move: CC_l; rewrite /CC; case C_l: (C l)=>[[Ty' CG]|//] H.
        move: H C_l=>[-><-] C_l {Ty'}; constructor.
        by move: PRJ; move=>/(_ l Ty CG L' C_l lC_l)=>[[PRJ|//]].
  Qed.

  Lemma QProj_unr CG Q :
    qProject (ig_end CG) Q -> qProject (rg_unr CG) Q.
  Proof.
    move=>/qProject_end_inv=>->.
    case: CG=>//=; first by constructor.
    move=> F T C; constructor; last by apply/not_fnd.
    move=>l Ty G; case: (C l)=>//[[Ty' G']]-[_ <-].
    by apply: qprj_end.
  Qed.

  Lemma local_runnable G P A G' :
    step A G G' -> Projection G P -> runnable A P.
  Proof.
  move=> ST; move: ST (step_cont_ipart ST).
  case: P => [E Q] ST PART [/=EPrj QPrj].
  elim: ST=>
    [ L F T C Ty G'' C_L
    | L F T C Ty G'' C_L
    | {}A l F T C0 C1 AF AT NE DOM_C STEP_C Ih
    | {}A l F T C0 C1 AT DOM_C STEP_C Ih
    | a CG G0 ST_G0 Ih
    ] /= in  E Q PART EPrj QPrj *.
  - rewrite /runnable/=.
    move: (eProj_part EPrj PART) => [L_F [IProj_F E_F]].
    move: (IProj_send1_inv IProj_F)=>[_ [lC [LF_msg [/(_ L Ty)-[DOM _] PRJ_C]]]].
    move: (DOM (ex_intro _ _ C_L)) => [L' lC_L].
    by rewrite E_F LF_msg lC_L !eq_refl.
  - rewrite /runnable/=.
    move: (eProj_part EPrj PART) => [L_F [IProj_F E_F]].
    move: (IProj_recv_inv IProj_F)=>[_ [lC [LF_msg [/(_ L Ty)-[DOM _] PRJ_C]]]].
    move: (DOM (ex_intro _ _ C_L)) => [L' lC_L].
    move: (qProject_Some_inv QPrj) => [Ty' [{}G [Q' [C_L' [/eqP-Q_FT _]]]]].
    rewrite E_F LF_msg lC_L !eq_refl/= Q_FT.
    by move: C_L C_L'=>-> [->]; rewrite !eq_refl.
  - move: EPrj=>/eProj_None_next-PRJ.
    move: NE=>[Ty [G0 C0l]].
    rewrite (runnable_next (A':=mk_act l_recv T F l Ty)) //.
    rewrite (runnable_next (A':=mk_act l_send F T l Ty)) //.
    move: (DOM_C l Ty)=>[/(_ (ex_intro _ _ C0l))-[G1 C1l] _].
    move: PRJ=>/(_ _ _ _ C0l)-PRJ.
    apply: (Ih _ _ _ _ C0l C1l _ _ _ PRJ);
      first by move: STEP_C=>/(_ _ _ _ _ C0l C1l)/step_cont_ipart.
    by move: QPrj=>/qProject_None_inv=>/(_ l Ty G0)-[_ /(_ C0l)].
  - move: EPrj=>/eProj_Some_next-PRJ.
    move: QPrj=>/qProject_Some_inv-[Ty [G0 [Q' [C0l [DEQ QPrj]]]]].
    rewrite (runnable_next_deq _ AT DEQ).
    rewrite (runnable_next (A':=mk_act l_recv T F l Ty)) //.
    move: Ih=>[_ [Ty' [G1 [G2 [C0l' [C1l [STEP Ih]]]]]]].
    move: C0l'; rewrite C0l =>[[ETy EG]].
    move: ETy EG Ih STEP C0l C1l=> <- <- Ih STEP C0l C1l {Ty' G1}.
    by apply: (Ih _ _ (step_cont_ipart STEP) (PRJ _ _ C0l)).
  - apply: (Ih _ _ (step_cont_ipart ST_G0)).
    + move: EPrj; rewrite /eProject=>[[P PRJ]].
      split; first by move=> p; rewrite -iPart_of_end_unr =>/P.
      move=>p /PRJ=>[[L [{}PRJ Ep]]]; exists L; split=>//.
      by apply/IProj_unr.
    + by apply/QProj_unr.
  Qed.

  Lemma runstep_qProj G P : forall A G',
    step A G G' -> Projection G P -> qProject G' (run_step A P).2.
  Proof.
    move=> A G' ST PRJ; move: (local_runnable ST PRJ).
    case: P PRJ=>[E Q] [EPRJ QPRJ]; elim: ST=>
    [ l F T C Ty G0 C_L
    | l F T C Ty G0 C_L
    | {}A l F T C0 C1 aF aT NE DOM STEP Ih
    | {}A l F T C0 C1 aT DOM STEP Ih
    | {}A CG G0 STEP Ih
    ]/= in EPRJ QPRJ *.
    - rewrite /runnable/run_step/=.
      case: (E.[? F])=>[L|//]; case: L=>[//|{}A p C0].
      case: (C0 l)=>[[Ty' L]|//]; case: ifP=>//=_ _.
      move: QPRJ=>/qProject_None_inv=>/(_ l Ty G0)-[QFT /(_ C_L)-QPRJ].
      apply: (qprj_some C_L _ QPRJ).
      rewrite /deq/enq/= QFT fnd_set !eq_refl remf1_set eq_refl remf1_id//.
      by rewrite -fndSome QFT.
    - rewrite /runnable/run_step/=.
      case: (E.[? T])=>[LT|//]; case: LT=>[//|{}A p C0].
      case: (C0 l)=>[[Ty' L]|//]; case: ifP=>//=_ _.
      move: QPRJ=>/qProject_Some_inv-[Ty'' [G1 [Q' [C_l [/eqP-DEQ PRJ]]]]].
      by move: C_l; rewrite C_L DEQ=>[[<- ->]]; rewrite !eq_refl/=.
    - admit.
    - admit.
    - admit.
  Qed.

  Lemma runstep_eProj G P : forall A G',
    step A G G' -> Projection G P -> eProject G' (run_step A P).1.
  Proof. Admitted.

  Lemma runstep_proj G P : forall A G',
    step A G G' -> Projection G P -> Projection G' (run_step A P).
  Proof.
  move=> A G' step pro; split.
  + by apply: (runstep_eProj step pro).
  + by apply: (runstep_qProj step pro).
  Qed.

(*
    move=> A G' ST Prj; split. move: (local_runnable ST Prj) => Run.
    elim: ST =>
    [ l F T C Ty G0 C_L
    | l F T C Ty G0 C_L
    | {}A l F T C0 C1 aF aT NE DOM STEP Ih
    | {}A l F T C0 C1 aT DOM STEP Ih
    | {}A CG G0 STEP Ih //
    ] in Prj Run *.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.*)


  Lemma Project_step G P : forall A G',
    step A G G' ->
    (* TODO: I deleted the well-formedness conditions. Add as required *)
    Projection G P ->
    exists P', Projection G' P' /\ lstep A P P'.
  Proof.
  move=> A G' ST Prj; exists (run_step A P); split.
  - apply/(runstep_proj ST Prj).
  - apply/run_step_sound/(local_runnable ST Prj).
  Qed.

    (* qProject G Q -> eProject G E
    -> exists E' Q', qProject G' Q' /\ eProject G' E'
       /\ lstep a (E, Q) (E', Q').
  Proof.
  move=> stephp.
  elim/step_ind: stephp E Q.
  + move=> L F T C Ty G0 contL E Q fincont wfc wf (*inPAR*) qpro epro.
    (*have Fin: F \in PAR.
      by apply: pin; apply: pof_from.*)
    move: (@eProject_send_none F T C E (*Fin*) epro).
    elim=> neq; elim=> lC; elim=> envF; elim=> samedom rall.
    move: (qProject_None_inv L Ty G0 qpro).
    elim; elim; move=> qpro0; move: (qpro0 contL)=> {}qpro0.
    have lT_aux: exists lT, lC L = Some (Ty, lT).
      move: samedom; rewrite /same_dom; move=> sd; rewrite -sd.
      by exists G0.
    move: lT_aux; elim=> lT lcontL.
    exists (E.[F <- lT]), (Q.[(F,T)<-[::(L,Ty)]]).
    split.
    * apply: (qprj_some neq contL _ qpro0); rewrite -(rwP eqP).
      apply: deq_singleton; rewrite -(rwP eqP).
      apply: (qProject_rcv_Free_None qpro wfc).
      move: wf; elim /wellFormed_inv =>//=.
      move=> wf p q CONT wfcont rfreecont [eq1 eq2 eq3].
      by rewrite -eq1 -eq2; apply rfree_send.
    split.
    * move: epro; elim=> allinPAR it.
      split; [by move=> p ip; apply allinPAR, (iPart_of_label_label _ ip)|].
      move=> p; case: (@eqP _ p F).
      - move=>-> pinPAR; exists lT; split.
        + by apply: (iprj_send2 neq samedom rall lcontL).
        + by rewrite fnd_set; case: ifP; rewrite eq_refl //=.
      - rewrite (rwP eqP); rewrite fnd_set; case: ifP =>//=.
        move=> hp1 _ pinPAR; move: (it _ pinPAR).
        elim=> lT0; elim=> pro_p E_P.
        exists lT0; split; [| by []].
        case: (@eqP _ p T).
        + move=> pT; move: pro_p; rewrite pT;  move=> pro_T.
          move: (IProj_recv_inv pro_T); elim=>_.
          elim=> lC0; elim=> L0eq; elim=> samedom0 rall0.
          rewrite L0eq; apply: (iprj_recv)=> //=.
          by rewrite eq_sym.
        + rewrite (rwP eqP); rewrite (rwP negP).
          move: (negbT hp1)=> neqpF neqpT.
          move: (IProj_mrg_inv pro_p neqpF neqpT); elim=> _.
          elim=> lC0; elim=> samedom0; elim=> rall0 mer.
          by apply: (iprj_mrg _ _ _ _ samedom0) =>//=.
    * apply: ls_send =>//=.
      - rewrite /enq (qProject_rcv_Free_None qpro) =>//=.
        move: wf; elim /wellFormed_inv =>//=.
        move=> wf p q CONT wfcont rfreecont [eq1 eq2 eq3].
        by rewrite -eq1 -eq2; apply rfree_send.
      - rewrite /do_act envF lcontL; case: ifP =>//=.
        by rewrite! eq_refl //=.
  + move=> L F T C Ty0 G0 contL E Q fincont wfc wf (*pin*) qpro epro.
    (*have Tin: T \in PAR.
      by apply: pin; apply: pof_to.*)
    move: (@eProject_recv _ F T C E (*Tin*) epro); elim=> neq.
    elim=> lC; elim=> envT; elim=> samedom rall.
    move: (qProject_Some_inv qpro); elim; elim.
    elim=> TTy; elim=> GG; elim=> Q'.
    elim; rewrite contL; move=> [eqTy eqG0]; rewrite eqTy eqG0.
    elim=> deqeq qpro'.
    have lT_aux: exists lT, lC L = Some (Ty0, lT).
      move: samedom; rewrite /same_dom; move=> sd; rewrite -sd.
      by exists G0.
    move: lT_aux; elim=> lT lcontL.
    exists (E.[T <- lT]), Q'.
    split; [by [] | split].
    * move: epro; elim=> allinPAR it.
      split; [by move=> p ip; apply allinPAR; rewrite -eqG0 in ip;
        apply: (ipof_cont (Some L) F T  contL ip)|].
      move=> p; case: (@eqP _ p T).
      - move =>-> pinPAR;  exists lT; split.
        + move: rall contL; rewrite /R_all eqG0; move=> rallu contL.
          by apply: (rallu _ _ _ _ contL lcontL).
        + by rewrite fnd_set; case: ifP; rewrite eq_refl //=.
      - rewrite (rwP eqP) (rwP negP); move=> neqpT pinPAR.
        rewrite eqG0 eqTy in contL.
        move: (it _ pinPAR); elim=> lT0; elim=> ipro eva.
        exists lT0; split.
        + case: (@eqP _ p F).
          * move=> eqpF; rewrite eqpF in ipro.
            move: (IProj_send2_inv ipro); elim=> _.
            elim=> lC0; elim=> Tyc; elim=> lC0L; elim=> samedom0.
            move: (samedom0 L Ty0); elim.
            elim; [|by rewrite eqTy; exists GG].
            move=> lT_aux; rewrite lC0L; move=> [eq1 eq2] _.
            rewrite eq1 eqTy in lC0L; move=> rall0.
            by rewrite eqpF; apply: (rall0 _ _ _ _ contL lC0L).
          * rewrite (rwP eqP); rewrite (rwP negP); move=> neqpF.
            move: (IProj_mrg_inv ipro neqpF neqpT); elim=> _.
            elim=> lC0; elim=> samedom0; elim=> rall0 mer.
            move: (samedom0 L Ty0); elim.
            elim; [|by rewrite eqTy; exists GG].
            move=> lTT lC0L _; apply: (@EqL_IProj _ _ lTT _).
            - by rewrite eqTy in lC0L; apply: (rall0 _ _ _ _ contL lC0L).
            - by apply: (mer _ _ _ lC0L).
        + rewrite fnd_set; case: ifP =>//=.
          rewrite -(rwP eqP); move=> eqpT; move: neqpT; rewrite eqpT.
          by rewrite -(rwP negP) eq_refl.
    * apply: ls_recv =>//=; rewrite /do_act envT lcontL eqTy => //=.
      by case: ifP; rewrite! eq_refl =>//=.
  + move=> aa F T C0 C1 nF nT sd01 ra01 IH E Q fincont wfc wf (*pin*) qpro epro.
    (*have subjin: subject aa \in PAR.
      apply: pin.
      apply: (@step_subject_part_of _ _ (rg_msg None F T C1)); [|by []].
      by apply: st_amsg1.*)

    (*
    L to D and F: from now on I'll keep track of the different steps
    for this case. Right now (06/05/2020) it appears to me that
    it is going to be a long one. I want to build E'.
    I have a plan (updated 18/05/2020).
    I will use the theorem I have proved for building
    finite functions, so that I can build E' extensionally,
    for each participant. I will extensively use the induction
    hypothesis.

New update (19/05/2020: change of plans! :)
)
*)
    have: exists E':{fmap role -> rl_ty}, (forall p : role, p \in PAR ->
      exists lT : rl_ty, IProj p (ig_msg None F T C1) lT /\
      E'.[? p] = Some lT).
      apply: (@all_fmap _ _ _
        (fun p oL => exists lT : rl_ty, IProj p (ig_msg None F T C1) lT /\
        oL = Some lT) ).
      move=> p.
      apply: (@exists_rel_finset_inhabited role PAR p (option rl_ty) None
        (fun p oL => exists lT : rl_ty, IProj p (ig_msg None F T C1) lT /\
        oL = Some lT) ).
      move=> pinPAR.
      suffices: exists (lT : rl_ty), IProj p (ig_msg None F T C1) lT.
        by elim=> lT ipro; exists (Some lT), lT; split.
      move: pinPAR; case: (@eqP _ p F).
      + move=>-> FinPAR; apply: iproj_send1_exists.
        - admit.
        - admit.

(*rewrite /same_dom /R_all.
          suffices: (exists KsL : lbl /-> mty * rl_ty,
            same_dom C1 KsL /\ R_all (IProj F) C1 KsL)





(*all_fset_option_map*)

    (*STEP 1. Selecting a label L_s.*)
    move: (ig_wfcont_msg_inv wfc); elim=> neq.
    elim; elim=> L_s; elim=> Ty_s; elim=> G0_s.
    elim=> C0L_s wfc_s wfcC0.

    (*STEP 2. The label L_s works also for C1.*)
    move: (sd01 L_s Ty_s); elim; elim; [|by exists G0_s].
    move=> G1_s C1L_s _.

    (*STEP 3. Getting well-formedness and projections for G0_s.*)
    move: wf; elim /wellFormed_inv =>//=; move=> wf.
  (*  move=> p q CONT wfC0 rfreeFTC0 [eq1 eq2 eq3].
    rewrite eq3 in wfC0; rewrite eq1 eq2 eq3 in rfreeFTC0.
    move: (wfC0 _ _ _ C0L_s) (rfreeFTC0 _ _ _ C0L_s).
    move=> wfG0_s rfreeFTG0_s; clear p q CONT eq1 eq2 eq3.

    (*STEP 4. Getting projection for G0_s.*)
    move: epro; rewrite /eProject.

    (*STEP 5. Getting queue-projection for G0_s.*)

    (*STEP 6. Getting E'_s from the induction hypothesis.*)
    *) *)
  Admitted.

 *)


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
