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

  Open Scope fmap.

  Definition eProject (G: ig_ty) (E : {fmap role -> rl_ty}) : Prop :=
    forall p, IProj p G (look E p).

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
        | F' T' C0
        | O F' T' C0
        | {}p O F' T' C0 {}L G Ty C0_L part_G
        ]; constructor.
    + by move: E=>[<- _ _]; constructor.
    + by move: E=>[_ _ <- _]; constructor.
    + move: E C0_L=>[_ _ _ <-] C_L {F' T' C0 O}.
      move: C_L; rewrite /C'; case C_L: (C L)=>[[{}Ty cG]|//] [_ cG_G].
      move: cG_G part_G=><-; case E: _ / =>[{}p cG' part_CG|||]//.
      move: E part_CG=>[<-] part_CG {cG'}.
      by apply/(pof_cont F T C_L)/part_CG.
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

  Lemma iproj_send1_exists p q KsG:
      p != q ->
      (exists KsL, same_dom KsG KsL /\ R_all (IProj p) KsG KsL) ->
      exists lT, IProj p (ig_msg None p q KsG) lT. (*rl_msg l_send q KsL*)
  Proof.
  move=> neq; elim=> KsL; elim=> sd rall.
  by exists (rl_msg l_send q KsL); apply: iprj_send1.
  Qed.


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

  (* Lemma eProj_igend_from F T C E : *)
  (*   eProject (ig_end (rg_msg F T C)) E -> *)
  (*   exists L : rl_ty, IProj F (ig_end (rg_msg F T C)) L /\ E.[? F] = Some L. *)
  (* Proof.  by move=>/(_ F (ipof_end (pof_from _ _ _))). Qed. *)

  (* Lemma eProj_igend_to F T C E : *)
  (*   eProject (ig_end (rg_msg F T C)) E -> *)
  (*   exists L : rl_ty, IProj T (ig_end (rg_msg F T C)) L /\ E.[? T] = Some L. *)
  (* Proof. by move=>/(_ T (ipof_end (pof_to _ _ _))). Qed. *)

  (* Lemma eProj_igmsg_to o F T C E : *)
  (*   eProject (ig_msg o F T C) E -> *)
  (*   exists L : rl_ty, IProj T (ig_msg o F T C) L /\ E.[? T] = Some L. *)
  (* Proof. by move=>/(_ T (ipof_to _ _ _ _)).  Qed. *)

  (* Lemma eProj_part p G E : *)
  (*     eProject G E -> iPart_of p G -> exists L, IProj p G L /\ E.[? p] = Some L. *)
  (* Proof. by move=>epro part; apply: epro. Qed. *)

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
    | F' T' C'
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
    case: A=>[a F T l Ty]; rewrite /do_act/look fnd_set => /=SUBJ.
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

  Lemma Proj_Some_next l F T C P :
    Projection (ig_msg (Some l) F T C) P ->
    forall Ty G,
      C l = Some (Ty, G) ->
      Projection G (run_step (mk_act l_recv T F l Ty) P).
  Proof.
    move=>[H qPRJ] Ty G Cl; move: (H T)=>PRJ.
    move: PRJ=>/IProj_recv_inv=>[[FT [CL [L_msg [DOM PRJ]]]]].
    move: (DOM l Ty)=>[/(_ (ex_intro _ _ Cl))-[L' CLl] _].
    move: qPRJ=>/qProject_Some_inv-[Ty' [G0 [Q [Cl' [DEQ qPRJ]]]]].
    move: Cl' DEQ qPRJ; rewrite Cl=> [[<-<-]] /eqP-DEQ QPRJ {Ty' G0}.
    rewrite /run_step/= L_msg CLl !eq_refl /= DEQ; split=>//.
    move=>p; case: (boolP (p == T)) =>[/eqP->|pT].
    - by rewrite /look fnd_set eq_refl; apply/(PRJ _ _ _ _ Cl CLl).
    - move: (H p)=>/IProj_send2_inv/(_ pT)-[_] [lC] [Ty0] [lCl] [DOM'] PRJ'.
      move: (DOM' l Ty)=>[/(_ (ex_intro _ _ Cl))-[L1 lCl'] _].
      move: lCl'; rewrite lCl=>[EQ]; move: EQ lCl=>[-> _] lCl {Ty0 L1}.
      rewrite  /look fnd_set (negPf pT) -/(look _ _).
      by apply: (PRJ' _ _ _ _ Cl lCl).
  Qed.

  Lemma look_comm E F L T (NEQ : F != T) :
    look E.[F <- L] T = look E T.
  Proof. by rewrite/look fnd_set eq_sym (negPf NEQ). Qed.


  Lemma Proj_None_next F T C P :
    Projection (ig_msg None F T C) P ->
    forall l Ty G,
      C l = Some (Ty, G) ->
      Projection G (run_step (mk_act l_recv T F l Ty)
                             (run_step (mk_act l_send F T l Ty) P)).
  Proof.
    move=>[H qPRJ] l Ty G Cl; move: (H F)=>PRJF.
    move: PRJF=>/IProj_send1_inv-[FT] [CF] [LF_E] [DOMF] PRJF.
    move: (DOMF l Ty) => [/(_ (ex_intro _ _ Cl))-[LF CFl] _].
    move: (H T)=>/IProj_recv_inv-[_] [CT] [LT_E] [DOMT] PRJT.
    move: (DOMT l Ty) => [/(_ (ex_intro _ _ Cl))-[LT CTl] _].
    move: qPRJ=>/qProject_None_inv-[PFT] qPRJ; split.
    - move=> p;
      case: (boolP (p == F)) =>[/eqP-> {p}|pF];
      [|case: (boolP (p == T)) =>[/eqP-> {pF p}|pT]].
      + (* p = F *)
        rewrite /look/run_step/= LF_E CFl !eq_refl/= look_comm // LT_E CTl.
        rewrite !eq_refl/= fnd_set (negPf FT) fnd_set eq_refl.
        by apply/(PRJF _ _ _ _ Cl).
      + (* p = T *)
        rewrite /look/run_step/= LF_E CFl !eq_refl /= look_comm // LT_E CTl.
        rewrite !eq_refl/= fnd_set eq_refl.
        by apply/(PRJT _ _ _ _ Cl).
      + (* T != p != F *)
        move: (H p)=>/IProj_mrg_inv/(_ pF)/(_ pT)-[_] [Cp] [DOMp] [PRJp] MRG.
        move: (DOMp l Ty) => [/(_ (ex_intro _ _ Cl))-[Lp' Cpl] _].
        move: (MRG _ _ _ Cpl)=>Lp_E.
        rewrite /run_step/= LF_E CFl !eq_refl/= look_comm// LT_E CTl.
        rewrite !eq_refl/= ?look_comm.
        by apply/(EqL_IProj _ Lp_E)/(PRJp _ _ _ _ Cl).
        by rewrite eq_sym.
        by rewrite eq_sym.
    - rewrite /run_step/= LF_E CFl !eq_refl /= look_comm // LT_E CTl !eq_refl/=.
      rewrite /enq PFT /deq fnd_set eq_refl /= remf1_set eq_refl.
      rewrite remf1_id; first by apply/qPRJ/Cl.
      by rewrite -fndSome PFT.
  Qed.

  Lemma doact_diff A E E' :
    do_act E A = Some E' -> exists L, E' = E.[subject A <- L].
  Proof.
    rewrite /do_act/look/=; case: A=>[a p q l Ty]; case Ep: E.[? p] =>[[|ap r C]|]//.
    by case Cl: C=>[[Ty' L]|//]; case: ifP=>//= _ [/esym-H]; exists L.
  Qed.

  Definition fst_eq (A B : eqType) (x y : option (A * B)) :=
    match x, y with
    | Some (a, _), Some (b, _) => a == b
    | None, None => true
    | _, _ => false
    end.

  Lemma runnable_next_queue A E (Q Q' : {fmap role * role -> seq (lbl * mty)}) :
    (forall p, fst_eq (deq Q (p, subject A)) (deq Q' (p, subject A)))  ->
    runnable A (E, Q) <-> runnable A (E, Q').
  Proof.
    move=> H; rewrite /runnable; case: do_act=>// _.
    case: A H=>[[//|] p q l Ty]/= /(_ q).
    case: deq=>[[[lQ TyQ] WQ]|]; case: deq=>[[[lQ' TyQ'] WQ']|]//=.
    by rewrite xpair_eqE=>/andP-[/eqP<- /eqP<-].
  Qed.

  Lemma runnable_next A A' P :
    subject A != subject A' ->
    (subject A != object A') || (act_ty A' == l_recv) ->
    runnable A P <-> runnable A (run_step A' P).
  Proof.
    case A => [a p q l Ty]; case A'=>[a' p' q' l' Ty']/= NEQ COND.
    rewrite /run_step/=; case: look =>[|a0 r0 C0]//.
    case C0l': C0=>[[Ty0 L0]|]//; case: ifP=>//.
    move=>/andP-[_ /eqP-H]; move: H C0l'=><- C0l' {a0 r0 Ty0}.
    move: COND; rewrite orbC; case: a'=>//= NEQ'.
    - rewrite -runnable_upd //; case: P=>[E Q]/=.
      apply/runnable_next_queue => r/=.
      rewrite /enq/=; case: Q.[? _] =>[W|].
      + rewrite /deq fnd_set xpair_eqE andbC (negPf NEQ') /andb.
        by case: Q.[? _] =>[[|V [|V' W']]|]/=.
      + rewrite /deq fnd_set xpair_eqE andbC (negPf NEQ') /andb.
        by case: Q.[? _] =>[[|V [|V' W']]|]/=.
    - case DEQ: deq=>[[[l0 Ty0] Q']|]//=; last by rewrite -runnable_upd//.
      rewrite -runnable_upd//.
      apply: runnable_next_queue=> r.
      move: DEQ; rewrite /deq/=.
      case EQ: P.2.[? _] => [[|V [|V' W]]|]//= [_ <-] {Q'}.
      * rewrite fnd_rem1 xpair_eqE negb_and orbC (negPf NEQ) /orb/negb.
        by case: P.2.[? _] =>[[|V0 [|V1 W0]]|]/=.
      * rewrite fnd_set xpair_eqE andbC (negPf NEQ) /andb.
        by case: P.2.[? _] =>[[|V0 [|V1 W0]]|]/=.
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
  move=> ST PRJ.
  (* case: P => [E Q] ST PART [/=EPrj QPrj]. *)
  elim: ST =>
    [ L F T C Ty G'' C_L
    | L F T C Ty G'' C_L
    | {}A l F T C0 C1 AF AT NE DOM_C STEP_C Ih
    | {}A l F T C0 C1 AT DOM_C STEP_C Ih
    | a CG G0 ST_G0 Ih
    ] /= in P PRJ *.
  - rewrite /runnable/=.
    move: (PRJ.1 F) => IProj_F.
    move: (IProj_send1_inv IProj_F)=>[_ [lC [LF_msg [/(_ L Ty)-[DOM _] PRJ_C]]]].
    move: (DOM (ex_intro _ _ C_L)) => [L' lC_L].
    by rewrite LF_msg lC_L !eq_refl /=.
  - rewrite /runnable/=.
    move: (PRJ.1 T) => IProj_F.
    move: (IProj_recv_inv IProj_F)=>[_ [lC [LF_msg [/(_ L Ty)-[DOM _] PRJ_C]]]].
    move: (DOM (ex_intro _ _ C_L)) => [L' lC_L].
    move: (qProject_Some_inv PRJ.2) => [Ty' [{}G [Q' [C_L' [/eqP-Q_FT _]]]]].
    rewrite LF_msg lC_L !eq_refl/= Q_FT.
    by move: C_L C_L'=>-> [->]; rewrite !eq_refl.
  - move: PRJ=>/Proj_None_next-PRJ.
    move: NE=>[Ty [G0 C0l]].
    rewrite (runnable_next (A' := mk_act l_send F T l Ty)) ?AF ?AT//.
    rewrite (runnable_next (A' := mk_act l_recv T F l Ty)) ?AF ?AT//.
    move: PRJ=>/(_ _ _ _ C0l)-PRJ.
    move: (DOM_C l Ty)=>[/(_ (ex_intro _ _ C0l))-[G1 C1l] _].
    by apply: (Ih _ _ _ _ C0l C1l _ PRJ).
  - move: PRJ.2=>/qProject_Some_inv-[Ty [G0 [Q' [C0l [DEQ QPrj]]]]].
    move: PRJ=>/Proj_Some_next-PRJ.
    move: Ih=>[_ [Ty' [G1 [G2 [C0l' [C1l [STEP Ih]]]]]]].
    move: C0l' C1l STEP Ih; rewrite C0l => [[<-<-] C1l STEP Ih].
    move: (PRJ Ty G0 C0l)=>{}PRJ.
    rewrite (runnable_next (A':=mk_act l_recv T F l Ty)) ?orbT //=.
    by apply: (Ih _ PRJ).
  - apply: Ih.
    move: PRJ=>[ePRJ qPRJ]; split.
    + move: ePRJ; rewrite /eProject=>[PRJ].
      move=>p; move: (PRJ p)=>IPRJ.
      by apply/IProj_unr.
    + by apply/QProj_unr.
  Qed.

  Lemma dom T T' (C0 : lbl /-> mty * T) (C1 : lbl /-> mty * T')
        (DOM : same_dom C0 C1)
    : forall l Ty G, C0 l = Some (Ty, G) -> exists G', C1 l = Some (Ty, G').
  Proof. by move=> l Ty; move: (DOM l Ty)=>[/(_ (ex_intro _ _ _))-H _]. Qed.

  Lemma look_same E F L : look E.[F <- L] F = L.
  Proof. by rewrite /look fnd_set eq_refl. Qed.

  Lemma Projection_send C l Ty G :
    C l = Some (Ty, G) ->
    forall F T P,
      Projection (ig_msg None F T C) P ->
      Projection (ig_msg (Some l) F T C) (run_step (mk_act l_send F T l Ty) P).
  Proof.
    move=>Cl F T P PRJ.
    move: (IProj_send1_inv (PRJ.1 F))=>[FT] [lCF] [EF] [DOMF] ALLF.
    move: (IProj_recv_inv (PRJ.1 T))=>[_] [lCT] [ET] [DOMT] ALLT.
    move: (dom DOMF Cl) (dom DOMT Cl) => [LF lCFl] [LT lCTl].
    rewrite /run_step/= EF lCFl !eq_refl/=.
    split.
    - move=>p; case: (boolP (p == F))=>[/eqP->{p}|];
      [|case: (boolP (p == T))=>[/eqP->{p} _|pT pF]].
      + by apply: (iprj_send2 FT FT DOMF ALLF); rewrite look_same; apply/lCFl.
      + rewrite look_comm //= ET.
        by apply: (iprj_recv _ _ DOMT ALLT); rewrite eq_sym.
      + rewrite look_comm //=; last by rewrite eq_sym.
        move: (IProj_mrg_inv (PRJ.1 p) pF pT)=>[_] [lCp] [DOMp] [ALLp] MRGp.
        move: (dom DOMp Cl) => [Lp lCpl].
        by apply/(EqL_IProj _ (MRGp _ _ _ lCpl))/(iprj_send2 pT FT DOMp ALLp lCpl).
    - move: (qProject_None_inv PRJ.2)=>[PFT] /(_ _ _ _ Cl)-QPRJ.
      apply: (qprj_some Cl _ QPRJ).
      rewrite /deq/enq/= PFT fnd_set eq_refl/= remf1_set eq_refl remf1_id //.
      by rewrite -fndSome PFT.
  Qed.

  Lemma Projection_recv C l Ty G :
    C l = Some (Ty, G) ->
    forall F T P,
      Projection (ig_msg (Some l) F T C) P ->
      Projection G (run_step (mk_act l_recv T F l Ty) P).
  Proof.
    move=>Cl F T P PRJ.
    move: (qProject_Some_inv PRJ.2)=>[TyQ] [GQ] [Q'].
    rewrite Cl=> [][] [<-<-] [/eqP-DEQ] QPRJ {TyQ GQ}.
    move: (IProj_recv_inv (PRJ.1 T))=>[FT] [lCT] [ET] [DOMT] ALLT.
    move: (IProj_send2_inv (PRJ.1 F) FT)=>[_] [lCF] [Ty'] [EF] [DOMF] ALLF.
    move: (dom DOMF Cl) (dom DOMT Cl) => [LF lCFl] [LT lCTl].
    move: lCFl; rewrite EF=>H; move: H EF=>[-> _] lCFl.
    rewrite /run_step/= ET lCTl !eq_refl/= DEQ.
    split=>//.
    move=>p; case: (boolP (p == F))=>[/eqP->{p}|];
             [|case: (boolP (p == T))=>[/eqP->{p} _|pT pF]].
    - rewrite look_comm; last by rewrite eq_sym.
      by apply: (ALLF _ _ _ _ Cl lCFl).
    - by rewrite look_same; apply: (ALLT _ _ _ _ Cl lCTl).
    - move: (IProj_send2_inv (PRJ.1 p) pT)=>[_] [lCp] [{}Ty'] [lCpl] [DOMp] ALLp.
      move: (dom DOMp Cl)=>[L'].
      rewrite lCpl=>[[ETy']] _ {L'}; move: ETy' lCpl=>-> lCpl.
      rewrite look_comm //; last by rewrite eq_sym.
      by apply/(ALLp _ _ _ _ Cl lCpl).
  Qed.

  Lemma do_actC E0 E1 E2 A1 A2 :
    subject A1 != subject A2 ->
    do_act E0 A1 = Some E1 ->
    do_act E0 A2 = Some E2 ->
    exists E3, do_act E1 A2 = Some E3 /\ do_act E2 A1 = Some E3.
  Proof.
    case: A1=>[a1 F1 T1 l1 Ty1]; case: A2=>[a2 F2 T2 l2 Ty2]/= FF.
    case E0F1: (look E0 F1) =>[|a3 q3 C3]//;
    case E0F2: (look E0 F2) =>[|a4 q4 C4]//.
    case C3l1: (C3 l1) => [[Ty3 L3]|]//; case: ifP=>// EQ [<-].
    case C4l2: (C4 l2) => [[Ty4 L4]|]//; case: ifP=>// EQ' [<-].
    rewrite /look !fnd_set eq_sym (negPf FF).
    move: E0F1; rewrite /look; case: E0.[? _] =>// L0->.
    move: E0F2; rewrite /look; case: E0.[? _] =>// {}L0->.
    rewrite C4l2 EQ' C3l1 EQ.
    rewrite setfC eq_sym (negPf FF).
    by exists (E0.[F2 <- L4]).[F1 <- L3].
  Qed.

  Lemma do_act_none E0 E1 A1 A2 :
    subject A1 != subject A2 ->
    do_act E0 A1 = Some E1 ->
    do_act E0 A2 = None ->
    do_act E1 A2 = None.
  Proof.
    case: A1=>[a1 F1 T1 l1 Ty1]; case: A2=>[a2 F2 T2 l2 Ty2]/= FF.
    case E0F1: (look E0 F1)=>[|a3 q3 C3]//.
    case C3l1: (C3 l1) => [[Ty3 L3]|]//; case: ifP=>// EQ [<-].
    case E0F2: (look E0 F2)=>[|a4 q4 C4]//.
    - rewrite /look fnd_set eq_sym (negPf FF).
      by move: E0F2; rewrite /look; case: (E0.[? F2])=>// L->.
    - case C4l2: (C4 l2) => [[Ty4 L4]|]//.
      + case: ifP=>// EQ0.
        move: E0F2; rewrite /look fnd_set eq_sym (negPf FF).
        by case: (E0.[? F2])=>//L'->; rewrite C4l2 EQ0.
      + move: E0F2; rewrite /look fnd_set eq_sym (negPf FF).
        by case: (E0.[? F2])=>//L'->; rewrite C4l2.
  Qed.

  Lemma enqC k k' (NEQ : k != k') Q v v' :
    enq (enq Q k v) k' v' = enq (enq Q k' v') k v.
  Proof.
    by rewrite /enq; case Qk: Q.[? k] => [W|];
       rewrite fnd_set eq_sym (negPf NEQ); case: Q.[? k'] =>[W'|];
       rewrite fnd_set (negPf NEQ) Qk //= setfC eq_sym (negPf NEQ).
  Qed.

  Lemma runnable_recv_deq F T l Ty P :
    runnable (mk_act l_recv F T l Ty) P ->
    exists Q W, deq P.2 (T, F) = Some ((l, Ty), Q) /\
              P.2.[? (T, F)] = Some ((l, Ty) :: W) /\
              forall k, k != (T, F) -> Q.[? k] = P.2.[? k].
  Proof.
    rewrite /runnable/=.
    case PF: (look P.1 F) =>[|a r C]//; case Cl: (C l) => [[Ty' L']|]//.
    case: ifP=>// COND; case DEQ: deq =>[[[l'] Ty'' Q]|]// /andP-[E1 E2].
    move:E1 E2 DEQ=>/eqP<-/eqP<-.
    rewrite /deq;case PTF: P.2.[? (T, F)] =>[[|[l0 Ty0] [|V' W]]|]//=[[<-<-]<-].
    - exists P.2.[~ (T, F)], [::]; do ! split=>//.
      by move=> k NEQ; rewrite fnd_rem1 NEQ.
    - exists P.2.[(T, F) <- V' :: W], (V'::W); do ! split=>//.
      by move=> k NEQ; rewrite fnd_set (negPf NEQ).
  Qed.

  Lemma deq_enq_neqC k k' (NEQ : k != k') v Q :
    deq (enq Q k v) k' =
    match deq Q k' with
    | Some (v', Q') => Some (v', enq Q' k v)
    | None => None
    end.
  Proof.
    by rewrite /deq/enq; (have NEQ': (k' != k) by (move: NEQ; rewrite eq_sym));
       case Qk': Q.[? k'] =>[[|v0 [|v1 w0] ]|]//=; case Qk: Q.[? k] =>[W|];
       rewrite fnd_set eq_sym (negPf NEQ) Qk' //= ?fnd_rem1 ?fnd_set (negPf NEQ)
               //= Qk ?remf1_set //= ?(negPf NEQ') //= setfC (negPf NEQ').
  Qed.

  Lemma deq_enq_sameC Q k' v' Q' :
    deq Q k' = Some (v', Q') ->
    forall k v, deq (enq Q k v) k' = Some (v', enq Q' k v).
  Proof.
    rewrite /deq; case Qk': Q.[? k'] => [[|V0 [|V0' W0]]|]//= [<-<-] {v' Q'} k v.
    - rewrite /enq; case Qk: Q.[? k] => [W|]//=; rewrite fnd_set;
      move: Qk' Qk; case: ifP=>[/eqP->|neq] Qk'; rewrite Qk'//=.
      + move=> [<-]/=; rewrite fnd_rem1 eq_refl /=.
        by rewrite setfC eq_refl setf_rem1.
      + by move=> Qk; rewrite fnd_rem1 eq_sym neq /= Qk remf1_set neq.
      + by move=> Qk; rewrite fnd_rem1 eq_sym neq /= Qk remf1_set neq.
    - rewrite /enq; case Qk: Q.[? k] => [W|]//=; rewrite fnd_set;
      move: Qk' Qk; case: ifP=>[/eqP->|neq] Qk'; rewrite Qk'//=.
      + move=> [<-]/=; rewrite fnd_set eq_refl /=.
        by rewrite setfC eq_refl setfC eq_refl.
      + by move=> Qk; rewrite fnd_set eq_sym neq /= Qk setfC neq.
      + by move=> Qk; rewrite fnd_set eq_sym neq /= Qk setfC neq.
  Qed.

  Lemma  deq_someC k0 k1 (NEQ : k0 != k1) Q v0 v1 Q0 Q1 :
    deq Q k0 = Some (v0, Q0) ->
    deq Q k1 = Some (v1, Q1) ->
    exists Q2, deq Q0 k1 = Some (v1, Q2) /\ deq Q1 k0 = Some (v0, Q2).
  Proof.
    rewrite /deq.
    case Qk0: Q.[? k0] => [[|V0 [|V0' W0]]|]//=;
    case Qk1: Q.[? k1] => [[|V1 [|V1' W1]]|]//= [<-<-] [<-<-] {v0 v1}.
    - exists Q.[~ k0].[~ k1].
      rewrite fnd_rem1 eq_sym NEQ Qk1 /= fnd_rem1 NEQ Qk0 /=; split=>//.
      by rewrite !remf_comp fsetUC.
    - exists Q.[~ k0].[k1 <- V1' :: W1].
      rewrite fnd_rem1 eq_sym NEQ Qk1 /=; split=>//.
      by rewrite fnd_set (negPf NEQ) Qk0 /= remf1_set (negPf NEQ).
    - exists (Q.[k0 <- V0' :: W0]).[~ k1].
      rewrite fnd_set eq_sym (negPf NEQ) Qk1; split=>//.
      by rewrite fnd_rem1 NEQ Qk0 /= remf1_set eq_sym (negPf NEQ).
    - exists (Q.[k0 <- V0' :: W0]).[k1 <- V1' :: W1].
      rewrite !fnd_set eq_sym (negPf NEQ) Qk0 Qk1 /=; split=>//.
      by rewrite setfC (negPf NEQ).
  Qed.

  Lemma  deq_noneC k0 k1 (NEQ : k0 != k1) Q v0 Q0 :
    deq Q k0 = Some (v0, Q0) ->
    deq Q k1 = None ->
    deq Q0 k1 = None.
  Proof.
    rewrite [in deq Q k0]/deq.
    by case Qk0: Q.[? k0] =>[[|V [|V' W]]|]//= [_ <-];
       rewrite /deq; case Qk1: Q.[? k1] =>[[|V1 [|V2 W1]]|]//=_;
       rewrite ?fnd_rem1 ?fnd_set eq_sym (negPf NEQ)/= Qk1.
  Qed.


  Lemma deq_neqC k k' (NEQ : k != k') Q :
    match deq match deq Q k' with | Some (_, Q') => Q' | None => Q end k with
    | Some (_, Q') => Q'
    | None => match deq Q k' with | Some (_, Q') => Q' | None => Q end
    end =
    match deq match deq Q k with | Some (_, Q') => Q' | None => Q end k' with
    | Some (_, Q') => Q'
    | None => match deq Q k with | Some (_, Q') => Q' | None => Q end
    end.
  Proof.
    case Qk': (deq Q k')=>[[v' Q']|];
      case Qk: (deq Q k)=>[[v Q'']|]; rewrite ?Qk' //.
    - by move: (deq_someC NEQ Qk Qk')=>[Q2] [->->].
    - by rewrite (deq_noneC _ Qk' Qk) // eq_sym.
    - by rewrite (deq_noneC NEQ Qk Qk').
  Qed.

  Lemma do_queueC A A' P :
    subject A != subject A' ->
    (subject A != object A') || (act_ty A' == l_recv) && runnable A' P ->
    do_queue (do_queue P.2 A') A = do_queue (do_queue P.2 A) A'.
  Proof.
    case: A=>[[] F T l Ty]; case: A'=>[[] F' T' l' Ty']//=.
    - by rewrite orbC/==> FF FT; rewrite enqC // xpair_eqE eq_sym negb_and FF.
    - move=> FF /orP-[FT|/runnable_recv_deq-[Q] [W] [DEQ] [LOOK] Q_EQ].
      + by rewrite deq_enq_neqC ?xpair_eqE ?negb_and ?FT //; case: deq=>[[]|].
      + by rewrite DEQ (deq_enq_sameC DEQ).
    - move=> FF; rewrite orbC eq_sym=>/= FT.
      by rewrite deq_enq_neqC ?xpair_eqE ?negb_and ?FT ?orbT//;case: deq=>[[]|].
    - by move=> FF _; apply: deq_neqC; rewrite xpair_eqE negb_and orbC FF.
  Qed.

  Lemma run_stepC A A' P :
    subject A != subject A' ->
    (subject A != object A') || ((act_ty A' == l_recv) && runnable A' P) ->
    run_step A (run_step A' P) = run_step A' (run_step A P).
  Proof.
    rewrite /run_step;
    case PA': (do_act P.lbl A')=>[E'|]/=; case PA: (do_act P.1 A)=>[E|]//=;
    rewrite ?PA' ?PA // => SUBJ.
    - move: (do_actC SUBJ PA PA')=> [E3] [->->] COND.
      by rewrite do_queueC.
    - by move: SUBJ; rewrite eq_sym=>SUBJ; rewrite (do_act_none SUBJ PA' PA).
    - by rewrite (do_act_none SUBJ PA PA').
  Qed.

  Lemma Projection_runnable l Ty G F T C P :
    C l = Some (Ty, G) ->
    Projection (ig_msg (Some l) F T C) P ->
    runnable (mk_act l_recv T F l Ty) P.
  Proof.
    move=> Cl [EPROJ QPROJ].
    move: EPROJ; rewrite /eProject=>/(_ T)-PRJ.
    move: PRJ=>/IProj_recv_inv=>[[FT] [lC] [E_lT] [DOM] PRJ].
    move: QPROJ=>/qProject_Some_inv=>[] [Ty'] [G0] [Q'] [Cl'] [DEQ] QPRJ.
    move: Cl' DEQ QPRJ; rewrite Cl =>[] [<-<-] /eqP-DEQ QPRJ {Ty' G0}.
    move: (DOM l Ty)=>[/(_ (ex_intro _ _ Cl))-[L' lCl] _].
    by rewrite /runnable/= E_lT lCl !eq_refl /= DEQ !eq_refl.
  Qed.

  Lemma Projection_unr G P :
    Projection (ig_end G) P -> Projection (rg_unr G) P.
  Proof.
    move=>[EPRJ QPRJ]; split.
    - move=>p; move: (EPRJ p)=>{}EPRJ.
      by apply: IProj_unr.
    - by apply: QProj_unr.
  Qed.

  Lemma Proj_send_undo l F T C Ty P :
    Projection (ig_msg (Some l) F T C) (run_step (mk_act l_send F T l Ty) P) ->
    Projection (ig_msg None F T C) P.
  Admitted.


  Lemma Proj_recv_undo l F T C Ty P G :
    C l = Some (Ty, G) ->
    Projection G (run_step (mk_act l_recv T F l Ty) P) ->
    Projection (ig_msg (Some l) F T C) P.
  Admitted.

  Lemma runstep_proj G P : forall A G',
    step A G G' -> Projection G P -> Projection G' (run_step A P).
  Proof.
    move=> A G' ST PRJ; elim: ST=>
    [ l F T C Ty G0 Cl
    | l F T C Ty G0 Cl
    | {}A l F T C0 C1 aF aT NE DOM STEP Ih
    | {}A l F T C0 C1 aT DOM STEP Ih
    | {}A CG G0 STEP Ih
    ]/= in P PRJ *.
    - by apply: (Projection_send Cl).
    - by apply: (Projection_recv Cl).
    - move: (dom DOM)=>DOMl.
      move: DOM=>/same_dom_sym/dom-DOMr.
      move: PRJ=>/Proj_None_next-PRJ.
      have {}Ih :
        forall (L : lbl) (Ty : mty) (G : ig_ty),
          C1 L = Some (Ty, G) ->
          Projection G (run_step A
                                 (run_step (mk_act l_recv T F L Ty)
                                           (run_step (mk_act l_send F T L Ty)
                                                     P))).
      { move=>l0 Ty G1 C1l; move: (DOMr _ _ _ C1l)=>[G0 C0l].
        move: (PRJ _ _ _ C0l)=>PRJ0.
        by apply: Ih; [apply: C0l | apply: C1l |].
      }
      move: NE=>[Tyl [G0 C0l]].
      move: (DOMl _ _ _ C0l) => [G1 C1l].
      (* TODO: We need to use this refined IH for the "undo" lemmas *)
      apply: (Proj_send_undo (l:=l) (Ty:=Tyl)).
      apply/(Proj_recv_undo (l:=l) (Ty:=Tyl) C1l).
      rewrite -(run_stepC (A:=A)) ?aT //= -(run_stepC (A:=A)) ?aF ?aT //= .
      by apply: Ih.
    - move: Ih=>[SAME_C] [Tyl] [G0] [G1] [C0l] [C1l] [STEP_G0_G1] Ih.
      move: (Projection_runnable C0l PRJ) => RUN.
      move: PRJ=>/Proj_Some_next-PRJ.
      move: (PRJ _ _ C0l)=> H0; move: (Ih _ H0)=>H1.
      (* TODO: use SAME_C in the undo step lemma *)
      apply/(Proj_recv_undo C1l).
      by rewrite -run_stepC //= RUN orbT.
    - by apply/Ih/Projection_unr.
  Qed.

  Theorem Project_step G P : forall A G',
    step A G G' ->
    Projection G P ->
    exists P', Projection G' P' /\ lstep A P P'.
  Proof.
  move=> A G' ST Prj; exists (run_step A P); split.
  - apply/(runstep_proj ST Prj).
  - apply/run_step_sound/(local_runnable ST Prj).
  Qed.
End TraceEquiv.

Print Assumptions Project_step.
