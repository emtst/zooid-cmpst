From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.

From Paco Require Import paco paco2.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.Common.

CoInductive rl_ty :=
| rl_end
| rl_msg (a : l_act) (R : role) (C : lbl -> option (mty * rl_ty))
.

Definition rlty_rel := rl_ty -> rl_ty -> Prop.
Inductive EqL_ (r : rlty_rel) : rlty_rel :=
| el_end : @EqL_ r rl_end rl_end
| el_msg a p C1 C2 :
    same_dom C1 C2 ->
    R_all r C1 C2 ->
    @EqL_ r (rl_msg a p C1) (rl_msg a p C2).
Hint Constructors EqL_.
Definition EqL L1 L2 := paco2 EqL_ bot2 L1 L2.
Derive Inversion EqL__inv with (forall r L0 L1, EqL_ r L0 L1) Sort Prop.

Lemma EqL_monotone : monotone2 EqL_.
Proof.
  move=>L1 L2 r r' E H; elim: E =>[|a p C1 C2 D E]//; constructor=>//.
  by move: E; rewrite /R_all=>E L Ty G G' /E-{E}E /E/H.
Qed.
Hint Resolve EqL_monotone.

Lemma EqL_refl CL : EqL CL CL.
Proof.
  move: CL {-1 3}CL (erefl CL).
  apply/paco2_acc=> r0 _ CIH CL CL'<- {CL'}.
  apply/paco2_fold.
  case: CL=>//a R C; constructor.
  - by move=> Lb Ty; split=>[[CL ->]|[CL ->]]; exists CL.
  - by move=> Lb Ty CG CG'-> [->]; right; apply: CIH.
Qed.

Lemma EqL_sym CL1 CL2 : EqL CL1 CL2 -> EqL CL2 CL1.
Proof.
  move: CL2 CL1; apply/paco2_acc=>r0 _ CIh L0 L1.
  move=>/(paco2_unfold EqL_monotone); elim/EqL__inv=>// _.
  + by move=> _ _; apply/paco2_fold; constructor.
  + move=> a p C1 C2 DOM ALL _ _ {L0 L1}.
    apply/paco2_fold; constructor; first by rewrite same_dom_sym.
    move=> l Ty L L' C2l C1l; right; apply/CIh.
    by move: (ALL l Ty _ _ C1l C2l)=>[].
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
