From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.

From Paco Require Import paco paco2.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.Common.

Require Import MPST.Global.Syntax.
Require Import MPST.Global.Tree.


Definition grel := g_ty -> rg_ty -> Prop.
Inductive g_unroll (r : grel) : grel :=
| gu_end :
    g_unroll r g_end rg_end
| gu_rec IG CG :
    r (g_open 0 (g_rec IG) IG) CG ->
    g_unroll r (g_rec IG) CG
| gu_msg FROM TO iCONT cCONT :
    same_dom (find_cont iCONT) cCONT ->
    R_all r (find_cont iCONT) cCONT ->
    g_unroll r (g_msg FROM TO iCONT) (rg_msg FROM TO cCONT).
Definition GUnroll IG CG : Prop := paco2 g_unroll bot2 IG CG.

Derive Inversion gunr_inv with (forall r G cG, g_unroll r G cG) Sort Prop.
Hint Constructors g_unroll.

Lemma gunroll_monotone : monotone2 g_unroll.
Proof.
  move=> IG CG r r' U H; move: IG CG U.
  elim=>[|V|G IH|F T C IH] CG;
    case E:_ _/ =>[|G' CG' R|F' T' C' CC DOM U]//.
  - by move: E R=>[<-]{G'} /H; constructor.
  - by constructor=>// l Ty IG {}CG H0 H1; apply/H/(U _ _ _ _ H0 H1).
Qed.
Hint Resolve gunroll_monotone.

Lemma gunroll_unfold r iG cG
  : paco2 g_unroll r iG cG -> @g_unroll (upaco2 g_unroll r) iG cG.
Proof. by move/(paco2_unfold gunroll_monotone). Qed.

Lemma g_unroll_rec (r : grel) n iG cG :
  (forall n IG CG, r IG CG -> paco2 g_unroll r (n_unroll n IG) CG) ->
  paco2 g_unroll r iG cG <-> paco2 g_unroll r (n_unroll n iG) cG.
Proof.
  move=> H; split.
  - elim: n =>// n Ih in iG cG *.
    move=> /gunroll_unfold-[]//=.
    + by apply/paco2_fold.
    + by move=>IG CG  [/Ih//|/H].
    + by move=>F T IC CC DOM UA; apply/paco2_fold; constructor.
  - elim: n =>// n Ih in iG cG *.
    by case: iG=>//= G H1; apply/paco2_fold; constructor; left; apply/Ih.
Qed.

Lemma GUnroll_ind n iG cG :
  GUnroll iG cG <-> GUnroll (n_unroll n iG) cG.
Proof. by apply/g_unroll_rec. Qed.

Lemma gen2 A B (x' : A) (y' : B) Q P :
  (forall x y, Q x y -> x = x' -> y = y' -> P) ->
  Q x' y' -> P.
Proof. by move=>H /H/( _ erefl erefl).  Qed.

Lemma r_in_unroll_msg r G p q Ks :
  GUnroll G (rg_msg p q Ks) ->
  guarded 0 G ->
  g_closed G ->
  (r == p) || (r == q) ->
  r \in participants G.
Proof.
  move=> GU GG CG r_pq; apply/(r_in_unroll_rec_depth).
  move: (unroll_guarded CG GG) r_pq => H.
  move: GU=>/(GUnroll_ind (rec_depth G)); move: H.
  move: (n_unroll _ G) => [|v|G'|p' q' Ks'].
  - by move=>_; apply: gen2=>iG cG /gunroll_unfold-[].
  - by move=>_; apply: gen2=>iG cG /gunroll_unfold-[].
  - by move=>/(_ G')/eqP.
  - move=>_; apply: gen2=>iG cG /gunroll_unfold-[]//.
    move=>F T IC CC DOM ALL E1 E2; move: E1 E2 DOM ALL=>[->->->][->->->].
    by move=>_ _; rewrite !in_cons orbA=>->.
Qed.

Lemma g_closed_unroll n iG : g_closed iG -> g_closed (n_unroll n iG).
Proof. by elim: n iG=>[|n Ih]//=; case=>//= iG /gopen_closed/Ih. Qed.


Lemma g_guarded_unroll iG :
  g_closed (g_rec iG) -> guarded 0 (g_rec iG) -> guarded 0 (unroll iG).
Proof.
  move=> C GG; have GG': (guarded 1 iG) by move:GG C=>/=; case: iG.
  move: (guarded_open 0 GG C GG')=>/guarded_depth_gt.
  by move=>/(_ _ _ (leq0n 1) (gopen_closed C)).
Qed.

Lemma g_guarded_nunroll n iG
  : g_closed iG -> guarded 0 iG -> guarded 0 (n_unroll n iG).
Proof.
  elim: n iG=>[|n Ih]//;case=>// iG CG /(g_guarded_unroll CG)/Ih-H/=.
  by apply/H/gopen_closed.
Qed.

CoFixpoint g_expand (g : g_ty) : rg_ty :=
  match n_unroll (rec_depth g) g with
  | g_msg F T Ks =>
    rg_msg F T
           (fun l =>
              match find_cont Ks l with
              | Some (Ty, G) => Some (Ty, g_expand G)
              | None => None
              end)
  | _ => rg_end
  end.

Lemma rgtyU G : G = match G with
                    | rg_msg F T C => rg_msg F T C
                    | rg_end => rg_end
                    end.
Proof. by case: G. Qed.

Definition g_expand' G :=
  match G with
  | g_msg F T Ks =>
    rg_msg F T (fun l : lbl => match find_cont Ks l with
                               | Some (Ty, G0) => Some (Ty, g_expand G0)
                               | None => None
                               end)
  | _ => rg_end
  end.

Lemma g_expand_once G : g_expand G = g_expand' (n_unroll (rec_depth G) G).
Proof.
  by rewrite (rgtyU (g_expand _)) /g_expand /g_expand'-rgtyU-/g_expand.
Qed.

Lemma g_expand_unr G :
  guarded 0 G ->
  g_closed G ->
  non_empty_cont G ->
  GUnroll G (g_expand G).
Proof.
  move=>gG cG NE; rewrite g_expand_once.
  move: {-1}(g_expand' _) (erefl (g_expand' (n_unroll (rec_depth G) G))).
  move=>CG ECG; move: G CG {ECG gG cG NE}(conj ECG (conj gG (conj cG NE))).
  apply/paco2_acc=>r _ /(_ _ _ (conj erefl (conj _ (conj _ _))))-CIH.
  move=> G CG [<-]{CG} [gG][cG][NE].
  case: G cG gG NE.
  - move=>_ _ _ /=; by apply/paco2_fold; constructor.
  - by move=>V /closed_not_var/(_ V)/eqP/(_ erefl).
  - move=>G cG gG nE /=;apply/paco2_fold.
    constructor; right; have gG': guarded 1 G by move: gG.
    rewrite (guarded_recdepth (m:=0) gG' _ (g_rec G)) //.
    apply/CIH.
    by apply/g_guarded_unroll.
    by apply/gopen_closed.
    by apply/ne_open.
  - move=>F T C cG gG NE; apply/paco2_fold; constructor.
    + move=>l Ty; case: find_cont=>[[Ty0 L0]|]//; split=>[][G]//[->] _.
      * by exists (g_expand L0).
      * by exists L0.
    + move=> l Ty G CG FND; rewrite FND=>[][<-]; right.
      move: cG; rewrite /g_closed/==>/flatten_eq_nil/member_map-cG.
      move: gG; rewrite /==>/forallbP/forall_member-gG.
      move: NE=>/==>/andP-[NE_C]/forallbP/forall_member/member_map-NE.
      move: (find_member FND)=>MEM.
      rewrite g_expand_once.
      by apply/(CIH _ (gG _ MEM) (cG _ MEM) (NE _ MEM)).
Qed.

Lemma expand_g_end g
      : is_end g -> g_expand g = rg_end.
Proof.
  rewrite (rgtyU (g_expand _))/=.
  suff: is_end g -> n_unroll (rec_depth g) g = g_end by move=>E /E->.
  move: {-1}(rec_depth g) (erefl (rec_depth g))=> n.
  elim: n g; first by case=>//.
  move=>n Ih; case=>//= g [] RD END; move: (recdepth_unroll END) RD=>->{}RD.
  by move: END=>/isend_unroll; apply/Ih.
Qed.
