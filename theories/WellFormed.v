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


  Definition rfree_rel := (role*role) -> rg_ty -> Prop.
  Inductive rFree_ (r: rfree_rel ) : rfree_rel :=
  | rfree_end p q: rFree_ r (p,q) rg_end
  | rfree_send p q CONT:
    ( forall l Ty G, CONT l = Some (Ty, G) ->
      r (p,q) G ) ->
    rFree_ r (p,q) (rg_msg None p q CONT)
  | rfree_diff p p' q q' o CONT:
    ( forall l Ty G, CONT l = Some (Ty, G) ->
      r (p,q) G ) ->
    (p,q) != (p',q') ->
    rFree_ r (p,q) (rg_msg o p' q' CONT)
  .
  Hint Constructors rFree_.
  Lemma rFree_monotone : monotone2 rFree_.
  Proof.
  elim=> p q G r r' rfr LE; move: rfr; case=>//.
  + move=> {}p {}q CONT hp; apply: rfree_send=> l Ty {}G eq.
    by apply (LE _ _ (hp _ _ _ eq)).
  + move=> {}p p' {}q q' o CONT hp neq; apply: rfree_diff =>//=.
    by move=> l Ty {}G eq; apply (LE _ _ (hp _ _ _ eq)).
  Qed.
  Hint Resolve rFree_monotone.
  Definition rcv_Free pq G := paco2 (rFree_) bot2 pq G.

  Definition RCV_Free G := (forall p q, rcv_Free (p,q) G).

  Inductive wform_ (r: rg_ty -> Prop ) : rg_ty -> Prop :=
  | wform_end: wform_ r rg_end
  | wform_send p q CONT:
    ( forall l Ty G, CONT l = Some (Ty, G) -> r G ) ->
    ( forall l Ty G, CONT l = Some (Ty, G) -> rcv_Free (p,q) G ) ->
    wform_ r (rg_msg None p q CONT)
  | wform_recv p q l CONT:
    ( forall l Ty G, CONT l = Some (Ty, G) -> r G ) ->
    wform_ r (rg_msg (Some l) p q CONT)
 .
  Hint Constructors wform_.
  Lemma wform_monotone : monotone1 wform_.
  Proof.
  move=> G r r' wfr LE; move: wfr; case=>//.
  + move=> p q CONT hp1 hp2; apply: (wform_send _ hp2).
    by move=> l Ty {}G eq; apply (LE _ (hp1 _ _ _ eq)).
  + move=> p q l CONT hp; apply: wform_recv.
    by move=> {}l Ty {}G eq; apply (LE _ (hp _ _ _ eq)).
  Qed.
  Hint Resolve wform_monotone.
  Definition well_Formed G := paco1 (wform_) bot1 G.

  Lemma wform_step a G G':
    well_Formed G -> step a G G' -> well_Formed G'.
  Proof.
  Admitted.

  Lemma wform_RCV_Free G: 
    RCV_Free G -> well_Formed G.
  Proof.
  Admitted.

  Lemma RCVFree_GUnroll iG G:
    GUnroll iG G -> RCV_Free G.
  Proof.
  Admitted.

  Lemma wform_GUnroll iG G:
    GUnroll iG G -> well_Formed G.
  Proof.
  by move=> hp; apply: wform_RCV_Free; apply: (RCVFree_GUnroll hp).
  Qed.




End WellFormed.