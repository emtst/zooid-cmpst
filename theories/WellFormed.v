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


(*second condition more beefy of wellformedness*)

  Definition rfree_rel := (role*role) -> ig_ty -> Prop.
  Inductive rcv_Free : rfree_rel :=
  | rfree_end p q cG: rcv_Free (p,q) (ig_end cG)
  | rfree_send p q CONT:
    ( forall l Ty G, CONT l = Some (Ty, G) ->
      rcv_Free (p,q) G ) ->
    rcv_Free (p,q) (ig_msg None p q CONT)
  | rfree_diff p p' q q' o CONT:
    ( forall l Ty G, CONT l = Some (Ty, G) ->
      rcv_Free (p,q) G ) ->
    (p,q) != (p',q') ->
    rcv_Free (p,q) (ig_msg o p' q' CONT)
  .
  Hint Constructors rcv_Free.

  Definition RCV_Free G := (forall p q, rcv_Free (p,q) G).

  Inductive well_Formed : ig_ty -> Prop :=
  | wform_end cG: well_Formed (ig_end cG)
  | wform_send p q CONT:
    ( forall l Ty G, CONT l = Some (Ty, G) -> well_Formed G ) ->
    ( forall l Ty G, CONT l = Some (Ty, G) -> rcv_Free (p,q) G ) ->
    well_Formed (ig_msg None p q CONT)
  | wform_recv p q l CONT:
    ( forall l Ty G, CONT l = Some (Ty, G) -> well_Formed G ) ->
    well_Formed (ig_msg (Some l) p q CONT)
 .


  Lemma wform_step a G G':
    well_Formed G -> step a G G' -> well_Formed G'.
  Proof.
  Admitted.

  Lemma wform_RCV_Free G: 
    RCV_Free G -> well_Formed G.
  Proof.
  Admitted.

(*The two following lemmas are now true by construction.
I left them there as a reminder for now; to be removed later.*)

  (*Lemma RCVFree_GUnroll iG G:
    GUnroll iG G -> RCV_Free G.
  Proof.
  Admitted.*)

  (*Lemma wform_GUnroll iG G:
    GUnroll iG G -> well_Formed G.
  Proof.
  by move=> hp; apply: wform_RCV_Free; apply: (RCVFree_GUnroll hp).
  Qed.*)




End WellFormed.