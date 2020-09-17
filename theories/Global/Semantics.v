From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.

From Paco Require Import paco paco2.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.Common.
Require Import MPST.Global.Tree.

Definition R_only (R : ig_ty -> ig_ty -> Prop)
           L0 (C C' : lbl -> option (mty * ig_ty)) :=
  (forall L1 K, L0 != L1 -> C L1 = Some K <-> C' L1 = Some K)
  /\ exists Ty G0 G1,
    C L0 = Some (Ty, G0)
    /\ C' L0 = Some (Ty, G1)
    /\ R G0 G1.

Unset Elimination Schemes.
Inductive step : act -> ig_ty -> ig_ty -> Prop :=
(* Basic rules *)
| st_send L F T C Ty G :
    C L = Some (Ty, G) ->
    step (mk_act l_send F T L Ty) (ig_msg None F T C) (ig_msg (Some L) F T C)
| st_recv L F T C Ty G :
    C L = Some (Ty, G) ->
    step (mk_act l_recv T F L Ty) (ig_msg (Some L) F T C) G
(* Struct *)
| st_amsg1 a L F T C0 C1 :
    subject a != F ->
    subject a != T ->
    (exists Ty G, C0 L = Some (Ty, G)) ->
    same_dom C0 C1 ->
    R_all (step a) C0 C1 ->
    step a (ig_msg None F T C0) (ig_msg None F T C1)
| st_amsg2 a L F T C0 C1 :
    subject a != T ->
    same_dom C0 C1 ->
    R_only (step a) L C0 C1 ->
    step a (ig_msg (Some L) F T C0) (ig_msg (Some L) F T C1)
| st_unr a CG G :
    step a (rg_unr CG) G ->
    step a (ig_end CG) G
.
Set Elimination Schemes.

Derive Inversion step_inv with (forall a G G', step a G G') Sort Prop.

Scheme step_ind1 := Induction for step Sort Prop.

Lemma step_ind
  (P : forall (a : act) (i i0 : ig_ty), step a i i0 -> Prop):
  (forall L F T C Ty G (e: C L = Some (Ty, G)),
    P (mk_act l_send F T L Ty) (ig_msg None F T C) (ig_msg (Some L) F T C)
      (st_send F T e) )
  ->
  (forall L F T C Ty G (e: C L = Some (Ty, G)),
    P (mk_act l_recv T F L Ty) (ig_msg (Some L) F T C) G (st_recv F T e))
  ->
  (forall a L F T C0 C1 (i : subject a != F) (i0 : subject a != T)
        (ne : exists Ty G, C0 L = Some (Ty, G))
        (s : same_dom C0 C1) (r : R_all (step a) C0 C1),
      (forall (L : lbl) (Ty : mty) (G G' : ig_ty)
         (e : C0 L = Some (Ty, G)) (e0 : C1 L = Some (Ty, G')),
       P a G G' (r L Ty G G' e e0)) ->
      P a (ig_msg None F T C0) (ig_msg None F T C1) (st_amsg1 i i0  ne s r))
  ->
  (*new property, mirroring R_only...*)
  (forall (a : act) (L : lbl) (F T : role)
        (C0 C1 : lbl -> option (mty * ig_ty)) (i : subject a != T)
        (s : same_dom C0 C1) (r : R_only (step a) L C0 C1),
    ((forall (L' : lbl) (K : mty * ig_ty),
    L != L' -> C0 L' = Some K <-> C1 L' = Some K) /\
    (exists (Ty : mty) (G0 G1 : ig_ty),
    C0 L = Some (Ty, G0) /\ C1 L = Some (Ty, G1)
    /\ (exists (r: step a G0 G1), P a G0 G1 r)))
    ->
    (*... with dependent types*)
    P a (ig_msg (Some L) F T C0) (ig_msg (Some L) F T C1)
        (st_amsg2 F i s r))
    ->
   (forall (a : act) (CG : rg_ty) (G : ig_ty) (s : step a (rg_unr CG) G),
      P a (rg_unr CG) G s -> P a (ig_end CG) G (st_unr s))
-> forall (a : act) (i i0 : ig_ty) (s : step a i i0), P a i i0 s.
Proof.
move=> P_send P_recv P_amsg1 P_amsg2 P_unr; fix Ih 4.
move=> a G G'; case; [by[]|by[]| | | ].
+ move=> a0 L F T C0 C1 nF nT NE samed rall.
  by apply: P_amsg1 =>//=.
+ move=> a0 L F T C0 C1 nT samed ronly.
  apply: P_amsg2 =>//=; split.
  - by move: ronly; rewrite /R_only; elim=> hp _.
  - move: ronly; rewrite /R_only; elim=> hp.
    elim=> Ty; elim=> G0; elim=> G1; elim=> C0L; elim=> C1L r.
    exists Ty, G0, G1; split; [by[]|split; [by[]| exists r]].
    by apply Ih.
+ move=> a0 CG G0 s; apply: P_unr =>//=.
Qed.

Definition gtrc_rel := trace act -> ig_ty -> Prop.
Inductive g_lts_ (r : gtrc_rel) : gtrc_rel :=
| eg_end : @g_lts_ r (tr_end act) (ig_end rg_end)
| eg_trans a t G G' :
    step a G G' ->
    r t G' ->
    g_lts_ r (tr_next a t) G.
Hint Constructors g_lts_.
Definition g_lts t g := paco2 g_lts_ bot2 t g.

Lemma g_lts_monotone : monotone2 g_lts_.
Proof. pmonauto. Qed.
Hint Resolve g_lts_monotone : paco.
