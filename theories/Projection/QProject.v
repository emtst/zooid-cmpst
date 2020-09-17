From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

From Paco Require Import paco paco2.

Require Import MPST.Common.
Require Import MPST.Global.
Require Import MPST.Local.

Open Scope fmap.

Definition qproj_rel := ig_ty -> {fmap role * role -> seq (lbl * mty) } -> Prop.
Inductive qProject : qproj_rel :=
| qprj_end G : qProject (ig_end G) [fmap]%fmap

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

Lemma qProject_None_inv_aux F T C Q GG:
  qProject GG Q ->
  GG = (ig_msg None F T C) ->
  Q.[? (F,T)] = None /\ forall l Ty G,
      (C l = Some (Ty, G) -> qProject G Q).
Proof.
  case =>//=.
  move=> p p' CONT Q0 IH neq [eq1 eq2 eq3].
  split; [by rewrite -eq1 -eq2| rewrite -eq3].
    by apply IH.
Qed.

Lemma qProject_None_inv F T C Q :
  qProject (ig_msg None F T C) Q ->
  Q.[? (F,T)] = None /\ forall l Ty G,
      (C l = Some (Ty, G) -> qProject G Q).
Proof.
    by move=> hp; move: (@ qProject_None_inv_aux F T C _ _ hp)=>H; apply/H.
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

Lemma deq_elsewhere Q Q' k0 k L Ty:
  deq Q' k0 == Some (L, Ty, Q) -> k != k0 ->
  Q'.[?k]=Q.[?k].
Proof.
  rewrite /deq; case E: (Q'.[? k0]) =>[qs|] //=; case qs => [|q qs0] //=.
  case: ifP; move=> _; rewrite -(rwP eqP); move=> [_ <-].
  + by rewrite fnd_rem1; case: ifP.
  + by rewrite fnd_set; case: ifP.
Qed.

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
