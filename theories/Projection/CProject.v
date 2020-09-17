From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.

From Paco Require Import paco paco1 paco2.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.Common.
Require Import MPST.Global.
Require Import MPST.Local.

Section CProject.
  Definition Merge (F : lbl -> option (mty * rl_ty)) (L : rl_ty) : Prop :=
    forall Lb Ty L', F Lb = Some (Ty, L') -> EqL L' L.

  Inductive WF_ (r : rg_ty -> Prop) : rg_ty -> Prop :=
  | WF_end : WF_ r rg_end
  | WF_msg F T C :
      F != T ->
      P_all r C ->
      (exists l Ty G, C l = Some (Ty, G)) ->
      WF_ r (rg_msg F T C).
  Definition WF := paco1 WF_ bot1.

  Lemma WF_mon : monotone1 WF_.
  Proof.
    move=> G r r' [].
    - by move=> _; apply/WF_end.
    - by move=> F T C FT ALL NE H; apply/WF_msg=>// l Ty {}G Cl; apply/H/ALL/Cl.
  Qed.

  Definition proj_rel := rg_ty -> rl_ty -> Prop.
  Inductive Proj_ (p : role) (r : proj_rel) : proj_rel :=
  | prj_end G : ~ part_of p G -> WF G -> Proj_ p r G rl_end
  | prj_send q KsG KsL :
      p != q ->
      same_dom KsG KsL ->
      R_all r KsG KsL ->
      Proj_ p r (rg_msg p q KsG) (rl_msg l_send q KsL)
  | prj_recv q KsG KsL :
      p != q ->
      same_dom KsG KsL ->
      R_all r KsG KsL ->
      Proj_ p r (rg_msg q p KsG) (rl_msg l_recv q KsL)
  | prj_mrg q s KsG KsL L :
      q != s ->
      p != q ->
      p != s ->
      (exists l Ty G, KsG l = Some (Ty, G)) ->
      P_all (part_of_all p) KsG ->
      same_dom KsG KsL ->
      R_all r KsG KsL ->
      Merge KsL L ->
      Proj_ p r (rg_msg q s KsG) L
  .
  Hint Constructors Proj_.
  Derive Inversion Proj__inv  with (forall p r G L, Proj_ p r G L) Sort Prop.

  Lemma Proj_monotone p : monotone2 (Proj_ p).
  Proof.
  rewrite /monotone2; move=> x0 x1 r r' it LE; move: it; case=>//.
  + by move=>G part; constructor.
  + move=> q KsG KsL neq samed HP; constructor =>//; move: HP; rewrite /R_all.
    move=> HP l Ty G L KsG_l KsL_l; apply: LE; by apply: (@HP l Ty G L KsG_l KsL_l).
  + move=> q KsG KsL neq samed rall; constructor =>//; move: rall; rewrite /R_all.
    move=> rall l t G L KsG_l KsL_l; apply: LE. by apply: (rall _ _ _ _ KsG_l KsL_l).
  + move=> q s KsG KsL L0 neq_qs neq_pq neq_ps NE parts samed rall merg.
    apply (@prj_mrg _ _ _ _ KsG KsL _) =>//; move: rall; rewrite /R_all.
    move=> rall l t G L KsG_l KsL_l; apply: LE; by apply: (rall _ _ _ _ KsG_l KsL_l).
  Qed.
  Hint Resolve Proj_monotone.
  Definition Project p CG CL := paco2 (Proj_ p) bot2 CG CL.

  Lemma Project_inv (p : role) (G : rg_ty) (L : rl_ty)
        (P : (let (sort, _) := role in sort) -> rg_ty -> rl_ty -> Prop) :
    (forall G0, G0 = G -> rl_end = L -> ~ part_of p G0 -> WF G0 -> P p G0 rl_end) ->
    (forall q CG CL,
       rg_msg p q CG = G -> rl_msg l_send q CL = L ->
       p != q -> same_dom CG CL -> R_all (Project p) CG CL ->
       P p (rg_msg p q CG) (rl_msg l_send q CL)) ->
    (forall q CG CL,
       rg_msg q p CG = G -> rl_msg l_recv q CL = L ->
       p != q -> same_dom CG CL -> R_all (Project p) CG CL ->
       P p (rg_msg q p CG) (rl_msg l_recv q CL)) ->
    (forall (q s : role) CG CL L0,
        q != s -> p != q -> p != s ->
        rg_msg q s CG = G -> L0 = L ->
        (exists l Ty G, CG l = Some (Ty, G)) ->
        P_all (part_of_all p) CG -> same_dom CG CL -> R_all (Project p) CG CL ->
        Merge CL L -> P p (rg_msg q s CG) L) ->
    Project p G L -> P p G L.
  Proof.
    move=> Hend Hsnd Hrcv Hmrg /(paco2_unfold (Proj_monotone (p:=p))).
    elim/Proj__inv =>/(paco2_fold _ _ _ _); rewrite -/(Project p G L) => PRJ.
    + by move=> G0 PART WF EQ1 EQ2; apply/Hend.
    + move=> q CG CL pq DOM ALL EQ1 EQ2; apply/Hsnd=>//.
      by move=>l Ty G0 G1 CGl CLl; move: (ALL l Ty G0 G1 CGl CLl)=>[|//].
    + move=> q CG CL pq DOM ALL EQ1 EQ2; apply/Hrcv=>//.
      by move=>l Ty G0 G1 CGl CLl; move: (ALL l Ty G0 G1 CGl CLl)=>[|//].
    + move=> q s CG CL L0 qs pq ps NE Part DOM ALL MRG EQ1 EQ2; apply/Hmrg=>//.
      by move=>l Ty G0 G1 CGl CLl; move: (ALL l Ty G0 G1 CGl CLl)=>[|//].
  Qed.

  Lemma samed_eql C0 C :
    R_all EqL C0 C ->
    same_dom C0 C ->
    forall l Ty L,
      C l = Some (Ty, L) -> exists L', C0 l = Some (Ty, L') /\ EqL L' L.
  Proof.
    move=> ALL DOM l Ty L Cl; move: (dom' DOM Cl)=>[L' C0l].
    by move: (ALL l Ty L' L C0l Cl)=> EQ; exists L'; split.
  Qed.

  Lemma EqL_Project p G lT lT':
    EqL lT lT' -> Project p G lT -> Project p G lT'.
  Proof.
  move=> eql prj; move: (conj eql prj) => {eql prj}.
  move=> /(ex_intro (fun lT=> _) lT) {lT}.
  move: G lT'; apply /paco2_acc; move=> r0 _ CIH G lT'.
  move: CIH=>/(_ _ _ (ex_intro _ _ (conj _ _)))-CIH.
  elim=> lT; elim; case lT'.
  + move=> eql; move: (EqL_r_end_inv eql); move=>->.
    rewrite /Project; move=> pro; move: paco2_mon; rewrite /monotone2.
    by move=> pamo; apply (pamo _ _ _ _ _ _ _ pro).
  + move=> a q C eql; move: (EqL_r_msg_inv eql).
    elim=> C0; elim=> samed; elim=> rall lTeq; rewrite lTeq.
    move=>PRJ; move: PRJ eql; elim/Project_inv=>//.
    * move=> q0 CG CL _ [<-->->] NE1 DOM ALL EQ_L {G q0}.
      apply/paco2_fold; constructor=>//; first by apply: (same_dom_trans DOM).
      move=>l Ty G G' CGl Cl; move: (samed_eql rall samed Cl)=>[L' [C0l EQ_L']].
      right; apply/CIH; first by apply/EQ_L'.
      by apply/(ALL _ _ _ _ CGl C0l).
    * move=> q0 CG CL _ [<-->->] NE1 DOM ALL EQ_L {G q0}.
      apply/paco2_fold; constructor=>//; first by apply: (same_dom_trans DOM).
      move=>l Ty G G' CGl Cl; move: (samed_eql rall samed Cl)=>[L' [C0l EQ_L']].
      right; apply/CIH; first by apply/EQ_L'.
      by apply/(ALL _ _ _ _ CGl C0l).
    * move=> r s CG CL L0 NE1 NE2 NE3 _ _  NE part DOM ALL MRG.
      move=> _ {G L0 lTeq lT}; apply/paco2_fold/prj_mrg=>//.
      - move=>l Ty G G' CGl Cl; right; apply/CIH; first by apply/EqL_refl.
        by apply/ALL; first by apply/CGl.
      - move=> l Ty L' CLl; move: (MRG l Ty  L' CLl).
        move=>/EqL_trans-H; apply: H; apply/paco2_fold; constructor=>//.
        by move=> l0 Ty0 L0 L1 C0l0 Cl0; left; apply/(rall _ _ _ _ C0l0 Cl0).
  Qed.

  (* FIXME: abstract all g_closed && guarded ... as "wf" to simplify statements*)

  Inductive IProj (p : role) : ig_ty -> rl_ty -> Prop :=
  | iprj_end CG CL :
      Project p CG CL ->
      IProj p (ig_end CG) CL
  | iprj_send1 q KsG KsL :
      p != q ->
      same_dom KsG KsL ->
      R_all (IProj p) KsG KsL ->
      IProj p (ig_msg None p q KsG) (rl_msg l_send q KsL)
  | iprj_send2 l t q r KsG KsL L :
      p != r ->
      q != r ->
      same_dom KsG KsL ->
      R_all (IProj p) KsG KsL ->
      KsL l = Some (t, L) ->
      IProj p (ig_msg (Some l) q r KsG) L
  | iprj_recv o q KsG KsL :
      p != q ->
      same_dom KsG KsL ->
      R_all (IProj p) KsG KsL ->
      IProj p (ig_msg o q p KsG) (rl_msg l_recv q KsL)
  (* | prj_end2 G : ~ In r G -> Proj_ r G rl_end *)
  | iprj_mrg q s KsG KsL L :
      q != s ->
      p != q ->
      p != s ->
      (* InAll r KsG -> *)
      (exists l Ty G, KsG l = Some (Ty, G)) ->
      same_dom KsG KsL ->
      R_all (IProj p) KsG KsL ->
      Merge KsL L ->
      IProj p (ig_msg None q s KsG) L
  .





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
  + move=> q s gC lC L neq1 neq2 neq3 NE samedom rall mer [eq1 eq2 eq3].
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
  + move=> q s gC lC L neq1 neq2 neq3 NE samedom rall mer [eq1 eq2 eq3 eq4].
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
    F != T /\
    (exists l Ty G, C l = Some (Ty, G)) /\
    (exists lC, same_dom C lC /\
      R_all (IProj p) C lC /\
      Merge lC CL).
  Proof.
  case =>//.
  + move=> q gC lC neq samedom rall neqF neqT [eq1 eq2 eq3].
    by move: neqF; rewrite eq1 -(rwP negP).
  + case=>// q cG cL neq samedom rall neqF neqT [eq1 eq2 eq3].
    by move: neqT; rewrite eq2 -(rwP negP).
  + move=>q s gC lC CL0 neq1 neq2 neq3 NE samedom rall mer neqF neqT [eq1 eq2 eq3].
    split; [by move: neq1; rewrite eq1 eq2|
            split;
            [ by move: eq3=><-; apply/NE
            | by exists lC; rewrite -eq3; split; [ |split; [|]]
           ]].
  Qed.

  Lemma IProj_mrg_inv p F T C CL:
    IProj p (ig_msg None F T C) CL ->
    p != F -> p != T ->
    F != T /\
    (exists l Ty G, C l = Some (Ty, G)) /\
    (exists lC, same_dom C lC /\
      R_all (IProj p) C lC /\
      Merge lC CL).
  Proof.
  by move=> hp neq1 neq2; apply: (IProj_mrg_inv_aux hp neq1 neq2).
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
  + move=> q s C lC lT0 neqqs neqpq neqps NE samed rall Ih mer lT' eqL.
    apply: (@iprj_mrg _ _ _ _
          (same_dom_const C lT') _ neqqs neqpq neqps)=>//.
    * by apply: same_dom_const_same_dom.
    * move=> L Ty G0 lTT' CL sdLa.
      move: (same_dom_const_some sdLa)=>->.
      move: (samed L Ty); elim=> sam _; move: sam.
      elim; [move=> lTT lCL | by exists G0].
      by apply: (Ih _ _ _ _ CL lCL) (EqL_trans (mer _ _ _ lCL) eqL).
    * by move=> Ln Tn lTn sdc; move: (same_dom_const_some sdc) =>->.
  Qed.

  Definition eProject (G: ig_ty) (E : {fmap role -> rl_ty}) : Prop :=
    forall p, IProj p G (look E p).

End CProject.
