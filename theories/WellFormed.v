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

Section WellFormed.


  (*Next thing is a furst condition of wellformednes, namely
continuations are never empty*)


  Definition g_pr :=  rg_ty -> Prop.
  Inductive g_wfcont_ (P : g_pr) : g_pr :=
  | g_wfcont_end : g_wfcont_ P rg_end
  | g_wfcont_msg F T C L Ty G:
      F !=T -> C L = Some (Ty, G) -> P G ->
      (forall LL TTy GG,
        C LL = Some (TTy, GG) -> P GG) ->
      g_wfcont_ P (rg_msg F T C).
  Hint Constructors g_wfcont_.
  Definition g_wfcont G := paco1 g_wfcont_ bot1 G.

  Lemma g_wfcont_monotone : monotone1 g_wfcont_.
  Proof.
  rewrite /monotone1; move=> G P P'; case=>//=.
  move=> F T C L Ty G0 neq CLeq wfG wfall hp.
  apply (g_wfcont_msg neq CLeq); [by apply hp|].
  move=> LL TTy GG CLL; apply hp.
  by apply (wfall _ _ _ CLL).
  Qed.
  Hint Resolve g_wfcont_monotone.

  Definition ig_pr :=  ig_ty -> Prop.
  Inductive ig_wfcont : ig_pr :=
  | ig_wfcont_end cG: g_wfcont cG -> ig_wfcont (ig_end cG)
  | ig_wfcont_msg o F T C L Ty G:
      F !=T -> C L = Some (Ty, G) -> ig_wfcont G ->
      (forall LL TTy GG,
        C LL = Some (TTy, GG) -> ig_wfcont GG) ->
      ig_wfcont (ig_msg o F T C).
  Hint Constructors ig_wfcont.




  Lemma g_wfcont_msg_inv_aux GG F T C:
    g_wfcont GG -> GG = (rg_msg F T C)-> F != T /\
    (exists L Ty G, C L = Some (Ty, G) /\ g_wfcont G) /\
    (forall LL TTy GG, C LL = Some (TTy, GG) -> g_wfcont GG).
  Proof.
  move=> wf; rewrite /g_wfcont in wf; punfold wf.
  move: wf =>
    [| F' T' C' L Ty G neq CL hp hpall [eq1 eq2 eq3]] //=.
  split; [by rewrite -eq1 -eq2|split].
  + exists L, Ty, G; split; [by rewrite -eq3|].
    by move: hp; rewrite /upaco1; elim.
  + move=> LL TTy GG' CLL; rewrite -eq3 in CLL.
    by move: (hpall _ _ _ CLL); rewrite /upaco1; elim.
  Qed.

  Lemma g_wfcont_msg_inv F T C:
    g_wfcont (rg_msg F T C)-> F != T /\
    (exists L Ty G, C L = Some (Ty, G) /\ g_wfcont G) /\
    (forall LL TTy GG, C LL = Some (TTy, GG) -> g_wfcont GG).
  Proof.
  by move=> hp; apply (@g_wfcont_msg_inv_aux _ F T _ hp).
  Qed.




  Lemma ig_wfcont_end_inv_aux GG CG:
    ig_wfcont GG -> GG = (ig_end CG)-> g_wfcont CG.
  Proof.
  case =>//=.
  by move=> cG wf [eq]; rewrite eq in wf.
  Qed.

  Lemma ig_wfcont_end_inv CG:
    ig_wfcont (ig_end CG)-> g_wfcont CG.
  Proof.
  by move=> hp; apply (@ig_wfcont_end_inv_aux _ _ hp).
  Qed.

  Lemma ig_wfcont_msg_inv_aux GG o F T C:
    ig_wfcont GG ->  GG = (ig_msg o F T C)-> F != T /\
    (exists L Ty G, C L = Some (Ty, G) /\ ig_wfcont G) /\
    (forall LL TTy GG, C LL = Some (TTy, GG) -> ig_wfcont GG).
  Proof.
  case =>//=.
  move=> o0 F0 T0 C0 L Ty G neq C0L wfG wfall [eq1 eq2 eq3 eq4].
  split; [by rewrite eq2 eq3 in neq|split].
  + by rewrite eq4 in C0L; exists L, Ty, G.
  + by rewrite eq4 in wfall.
  Qed.

  Lemma ig_wfcont_msg_inv o F T C:
    ig_wfcont (ig_msg o F T C)-> F != T /\
    (exists L Ty G, C L = Some (Ty, G) /\ ig_wfcont G) /\
    (forall LL TTy GG, C LL = Some (TTy, GG) -> ig_wfcont GG).
  Proof.
  by move=> hp; apply (@ig_wfcont_msg_inv_aux _ o F T _ hp).
  Qed.


  Lemma ig_wfcont_rg_unr CG:
    ig_wfcont (ig_end CG)
    -> ig_wfcont (rg_unr CG).
  Proof.
  case CG =>//=; move=> F T C iwf.
  move: (g_wfcont_msg_inv (ig_wfcont_end_inv iwf)).
  elim=>neq; elim; elim=>L; elim=>Ty; elim=>cG; elim=>CL wfG hp.
  apply: (@ig_wfcont_msg _ _ _ _ L Ty (ig_end cG) neq).
  + by rewrite CL.
  + by apply ig_wfcont_end.
  + move=> LL TTy GG; case E: (C LL)=> [P0|] //=.
    move: E; case P0; move=> Ty0 cG0 CLL [eqTy eqGG].
    by rewrite -eqGG; apply: ig_wfcont_end (hp _ _ _ CLL).
  Qed.


(*second condition more beefy of wellformedness*)

  Definition rfree_rel := role -> role -> ig_ty -> Prop.
  Inductive rcv_Free : rfree_rel :=
  | rfree_end p q cG: rcv_Free p q (ig_end cG)
  | rfree_send p q CONT:
    ( forall l Ty G, CONT l = Some (Ty, G) ->
      rcv_Free p q G ) ->
    rcv_Free p q (ig_msg None p q CONT)
  | rfree_diff p p' q q' o CONT:
    ( forall l Ty G, CONT l = Some (Ty, G) ->
      rcv_Free p q G ) ->
      (p != p') || (q != q') ->
      rcv_Free p q (ig_msg o p' q' CONT)
  .
  Hint Constructors rcv_Free.

  Derive Inversion rcvFree_inv with (forall p q G, rcv_Free p q G) Sort Prop.

  Definition RCV_Free G := (forall p q, rcv_Free p q G).

  Inductive well_formed : ig_ty -> Prop :=
  | wform_end cG: well_formed (ig_end cG)
  | wform_send p q CONT:
    ( forall l Ty G, CONT l = Some (Ty, G) -> well_formed G ) ->
    ( forall l Ty G, CONT l = Some (Ty, G) -> rcv_Free p q G ) ->
    well_formed (ig_msg None p q CONT)
  | wform_recv p q l CONT:
    ( forall l Ty G, CONT l = Some (Ty, G) -> well_formed G ) ->
    well_formed (ig_msg (Some l) p q CONT)
 .

  Derive Inversion wellFormed_inv with (forall G, well_formed G) Sort Prop.

  Lemma wform_unr CG : well_formed (rg_unr CG).
  Proof.
    case: CG=>[|F T C]/=; constructor =>//=; move=>l Ty G;
      case: (C l) =>[[MTy G'']|]//[_<-]; by constructor.
  Qed.

  Lemma rcvFree_cont F T F' T' C
    : rcv_Free F T (ig_msg None F' T' C) ->
      forall L Ty G, C L = Some (Ty, G) -> rcv_Free F T G.
  Proof.
    elim/rcvFree_inv=>
      [ //
      | _ p q C' H _ _ [_ _ C_C']
      | _ p p' q q' o C' H _ _ _ [_ _ _ C_C']
      ]; by move: C_C' H=>->.
  Qed.

  Lemma rfree_unr F T CG : rcv_Free F T (rg_unr CG).
  Proof.
    case: CG=>[|F' T' C]//=; case: (boolP ((F == F') && (T == T'))).
    + move=>/andP-[/eqP<-/eqP<-]; apply/rfree_send=> L Ty G.
      by case: (C L)=>[[Ty' CG] [Ty_Ty' <-]|]//.
    + rewrite negb_and=>NEQ; apply/rfree_diff=>// L Ty G.
      by case: (C L)=>[[Ty' CG] [_ <-]|]//.
  Qed.

  Lemma rfree_step G G' a F T
    (a_F: subject a != F) (a_T: subject a != T)
    : step a G G' ->
      rcv_Free F T G ->
      rcv_Free F T G'.
  Proof.
    move=>ST; elim: ST a_F a_T
      =>[ L F' T' C Ty G0 C_L
        | L F' T' C Ty G0 C_L
        | {}a l F' T' C0 C1 a_F' a_T' NE dom_C0_C1 step_C0_C1 Ih
        | {}a L F' T' C0 C1 a_T' dom_C0_C1 step_C0_C1 Ih
        | {}a CG G0 step_a0_CG_G0 Ih
        ]/= a_F a_T.
      - elim/rcvFree_inv => _ //=;
          first by move=>p q C' _ p_F q_T [/esym/eqP]; rewrite (negPf a_F).
        move=> p p' q q' o C' H Neq p_F q_T [_ F_p' q_T' EC']  {p_F q_T p q o}.
        move: F_p' q_T' Neq EC' H=>->->T_T' {q'} -> H {C'}.
        by apply/rfree_diff=>//; rewrite eq_sym.
      - elim/rcvFree_inv => _ //= p p' q q' o C' H Neq _ _ [_ p'_F' q'_T' C'_C] {p q}.
        by move: p'_F' q'_T' C'_C Neq H =>->->->Neq /(_ _ _ _ C_L).
      - move: Ih; case: (boolP ((F == F') && (T == T'))).
        + move=>/andP-[/eqP<-/eqP<-] Ih /rcvFree_cont-H.
          apply: rfree_send=> L Ty G'' C1_L.
          move: (ex_intro (fun G''=>_) G'' C1_L)=>/dom_C0_C1-[G''' C0_L].
          move: (H _ _ _ C0_L)=>RF_G'''; by apply: (Ih _ _ _ _ C0_L C1_L).
        + rewrite negb_and=>NEQ Ih /rcvFree_cont-H.
          apply:rfree_diff=>// L Ty G'' C1_L.
          move: (ex_intro (fun G=>_) G'' C1_L)=>/dom_C0_C1-[G''' C0_L].
          by apply/(Ih _ _ _ _ C0_L C1_L a_F a_T)/(H _ _ _ C0_L).
      - elim/rcvFree_inv=>//= _ p p' q q' o C H NEQ _ _ [_ p'_F' q'_T' C_C0] {o p q}.
        move: p'_F' q'_T' C_C0 NEQ H=>->->->NEQ H { p' q' C}.
        apply: rfree_diff=>// L' Ty G'' C1_L'.
        move: Ih=>[same_K [Ty' [G0 [G1 [C0_L [C1_L [ST /(_ a_F a_T)-Ih]]]]]]].
        case: (boolP (L == L'))=>[/eqP-L_L'|L_L'].
        + move: L_L' C1_L'=><-; rewrite C1_L=>[[Eq_Ty Eq_G]].
          by move: Eq_G Eq_Ty Ih C0_L C1_L=>->->Ih /H/Ih-RF_G'' _.
        + by apply/H/(same_K _ _ L_L')/C1_L'.
      - move=>_; apply/(Ih a_F a_T)/rfree_unr.
  Qed.

  Lemma wform_step a G G':
    well_formed G -> step a G G' -> well_formed G'.
  Proof.
    move=>WF_G STEP;
      elim: STEP
        =>[ L F T C Ty G0 C_L
          | L F T C Ty G0 C_L
          |{}a l F T C0 C1 a_F a_T NE dom_C0_C1 step_C0_C1 Ih
          |{}a L F T C0 C1 a_T dom_C0_C1 step_C0_C1 Ih
          |{}a CG G0 step_a0_CG_G0 Ih
          ] in WF_G *.
    - case E: _ / WF_G => [//|F' T' C' Wf _|//].
      move: E Wf=>[_ _ <-] Wf; by constructor.
    - case E: _ / WF_G => [//|//|L' F' T' C' Wf].
      by move: E Wf=>[_ _ _ <-] /(_ _ _ _ C_L).
    - case E: _ / WF_G =>[//|F' T' C' Wf_G Rf_G|//].
      move: E Wf_G Rf_G=>[<-<-<-] Wf_G Rf_G {F' T' C'}.
      constructor.
      + move=>L' Ty G'' C1_L'.
        move: (ex_intro (fun G''=>_) G'' C1_L')=>/dom_C0_C1-[G0'' C0_L'].
        by apply/(Ih _ _ _ _ C0_L' C1_L')/Wf_G/C0_L'.
      + move=>L' Ty G'' C1_L'.
        move: (ex_intro (fun G''=>_) G'' C1_L')=>/dom_C0_C1-[G0'' C0_L'].
        apply/(rfree_step a_F a_T (step_C0_C1 _ _ _ _ C0_L' C1_L')).
        by apply/Rf_G/C0_L'.
    - case E: _ / WF_G =>[//|//|F' T' L' C' WF].
      move: E WF=>[_ _ _ <-] WF {L' F' T'}.
      move: Ih=>[same_L [Ty [G0 [G1 [C0_L [C1_L [ST Ih]]]]]]].
      constructor=> L' Ty' G'' C1_L'; case: (boolP (L == L'))=>[/eqP-L_L'|].
      + move: L_L' C1_L' =><-; rewrite C1_L => [[Ty_Ty' G1_G']].
        by move: G1_G' => <-; apply/Ih/WF/C0_L.
      + by move=> L_L'; apply/WF/(same_L _ _ L_L')/C1_L'.
    - by apply/Ih/wform_unr.
  Qed.

  Lemma wform_RCV_Free G:
    RCV_Free G -> well_formed G.
  Proof.
    elim: G=>[CG _|ST FROM TO C Ih]; first by constructor.
    move=> RF; have {}RF: forall L Ty G, C L = Some (Ty, G) -> RCV_Free G.
    { move=> L Ty G H P Q; move: (RF P Q).
      elim/rcvFree_inv=>// _.
      - move=> P' Q' C' RF_C _ _ [_ _ _ C_C'].
        move: C_C' RF_C=>->RF_C; by apply/RF_C/H.
      - move=> P' P'' Q' Q'' O_L C' RF_C _ _ _ [_ _ _ C_C'].
        move: C_C' RF_C=>->RF_C; by apply/RF_C/H.
    }
    case: ST=>[L|]; constructor=> L' Ty G;
      move: (RF L') (Ih L'); case E: (C L')=>[[Ty' G']|]//= RF_L' Ih_L' [_ <-].
    + by apply/(Ih_L' _ _ erefl)=> P Q; apply/(RF_L' Ty' G' erefl).
    + by apply/(Ih_L' _ _ erefl)=> P Q; apply/(RF_L' Ty' G' erefl).
    + by apply/(RF_L' Ty' G' erefl).
  Qed.

(*The two following lemmas are now true by construction.
I left them there as a reminder for now; to be removed later.*)

  (*Lemma RCVFree_GUnroll iG G:
    GUnroll iG G -> RCV_Free G.
  Proof.
  Admitted.*)

  (*Lemma wform_GUnroll iG G:
    GUnroll iG G -> well_formed G.
  Proof.
  by move=> hp; apply: wform_RCV_Free; apply: (RCVFree_GUnroll hp).
  Qed.*)

End WellFormed.
