From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.

From Paco Require Import paco paco2.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.Atom.
Require Import MPST.AtomSets.
Require Import MPST.Forall.
Require Import MPST.Actions.

Section Syntax.
  (**
   * Global Types
   *)
  Inductive g_ty :=
  | g_end
  | g_var (VAR : nat)
  | g_rec (GT : g_ty)
  | g_msg (FROM TO : role) (CONT : seq (lbl * (mty * g_ty))).

  Open Scope mpst_scope.

  Fixpoint depth_gty (a : g_ty) :=
    match a with
    | g_end
    | g_var _ => 0
    | g_rec G => (depth_gty G).+1
    | g_msg _ _ K => (maximum (map (fun x=> depth_gty x.cnt) K)).+1
    end.

  Fixpoint participants (G : g_ty) :=
    match G with
    | g_end
    | g_var _ => [::]
    | g_rec G => participants G
    | g_msg p q Ks => p::q::flatten [seq participants K.cnt | K <- Ks]
    end.

  Fixpoint flat_set (A : choiceType) (L : seq {fset A}) :=
    match L with
    | [::] => fset0
    | x::xs => x `|` flat_set xs
    end%fset.

  Fixpoint parts_set (G : g_ty) :=
    match G with
    | g_end
    | g_var _ => fset0
    | g_rec G => parts_set G
    | g_msg p q Ks => p |` (q |` flat_set [seq parts_set K.cnt | K <- Ks])
    end%fset.

  Lemma gty_ind1 :
    forall (P : g_ty -> Prop),
      P g_end ->
      (forall v, P (g_var v)) ->
      (forall G, P G -> P (g_rec G)) ->
      (forall p q Ks, (forall K, member K Ks -> P K.cnt) ->
                        P (g_msg p q Ks)) ->
      forall g : g_ty, P g.
  Proof.
    move=> P P_end P_var P_rec P_msg; fix Ih 1; case.
    + by apply: P_end.
    + by apply: P_var.
    + by move=>G; apply: P_rec.
    + move=>p q Ks; apply: P_msg.
      by apply/forall_member; elim: Ks.
  Qed.

  Fixpoint eq_g_ty (a b : g_ty) :=
    match a, b with
    | g_end, g_end => true
    | g_var v1, g_var v2 => v1 == v2
    | g_rec G1, g_rec G2 => eq_g_ty G1 G2
    | g_msg p1 q1 Ks1, g_msg p2 q2 Ks2 =>
        (p1 == p2)
        && (q1 == q2)
        && (fix eqL Ks1 Ks2 :=
              match Ks1, Ks2 with
              | [::], [::] => true
              | K1::Ks1, K2::Ks2 => (K1.lbl == K2.lbl)
                                      && (K1.mty == K2.mty)
                                      && eq_g_ty K1.cnt K2.cnt
                                      && eqL Ks1 Ks2
              | _, _ => false
              end) Ks1 Ks2
    | _, _ => false
    end.

  Definition eq_alt (l r : lbl * (mty * g_ty)) :=
    (l.lbl == r.lbl) && (l.mty == r.mty) && eq_g_ty l.cnt r.cnt.

  Lemma eqgty_all p1 q1 (Ks1 : seq (lbl * (mty * g_ty))) p2 q2 Ks2 :
    eq_g_ty (g_msg p1 q1 Ks1) (g_msg p2 q2 Ks2) =
    (p1 == p2) && (q1 == q2) && all2 eq_alt Ks1 Ks2.
  Proof.
    rewrite /=; do 2 (case: eqP=>///= _).
    by elim: Ks1 Ks2=>[|Ks1 K1 Ih]; case=>[|Ks2 K2]//; rewrite Ih.
  Qed.

  Lemma g_ty_eqP : Equality.axiom eq_g_ty.
  Proof.
    rewrite /Equality.axiom; fix Ih 1 => x y.
    case x =>[|vl| Gl |pl ql Ksl]; case y =>[|vr| Gr |pr qr Ksr];
      try (by constructor).
    + by rewrite /eq_g_ty; case: eqP=>[->|H];constructor=>//[[]].
    + by rewrite /=; case: Ih=>[->|H];constructor=>//[[]].
    + rewrite eqgty_all; do 2 (case: eqP=>[<-|H];[|constructor=>[[]]//] =>/=).
      elim: Ksl Ksr =>[|[ll [tl Gl]] Ksl IhKs].
      - case; try (by constructor).
      - move=>[|[lr [tr Gr] Ksr]/=]; first (by constructor).
        rewrite /eq_alt/=; do 2 (case: eqP=>[->|F];[|constructor=>[[/F]]//]).
        case: Ih=>[->|F]/=;[|constructor=>[[/F]]//].
        by case: IhKs=>[[]<-|F]; constructor=>//[[F']]; move: F' F=>->.
  Qed.

  Definition g_ty_eqMixin := EqMixin g_ty_eqP.
  Canonical g_ty_eqType := Eval hnf in EqType g_ty g_ty_eqMixin.

  Lemma alt_eqP : Equality.axiom eq_alt.
  Proof.
    rewrite /Equality.axiom/eq_alt; move=>[l1  [t1 Ks1]] [l2 [t2 Ks2]]/=.
    do 2 (case: eqP=>[<-|H]; last (by apply: ReflectF => [[/H]])).
    by case: g_ty_eqP=>[<-|H]; last (by apply: ReflectF =>[[/H]]); apply: ReflectT.
  Qed.

  Lemma gty_ind2 :
    forall (P : g_ty -> Prop),
      P g_end ->
      (forall v, P (g_var v)) ->
      (forall G, P G -> P (g_rec G)) ->
      (forall p q Ks, Forall (fun K => P K.cnt) Ks -> P (g_msg p q Ks)) ->
      forall G : g_ty, P G.
  Proof.
    move=> P P_end P_var P_rec P_msg; elim/gty_ind1=>//.
    by move=> p q Ks /forall_member; apply: P_msg.
  Qed.

  Fixpoint g_open (d : nat) (G2 : g_ty) (G1 : g_ty) :=
    match G1 with
    | g_end => G1
    | g_var v => if v == d then G2 else G1
    | g_rec G => g_rec (g_open d.+1 G2 G)
    | g_msg p q Ks =>
      g_msg p q [seq (K.lbl, (K.mty, g_open d G2 K.cnt)) | K <- Ks]
    end.
  Notation "{ k '~>' v } G":= (g_open k v G) (at level 30, right associativity).
  Notation "G '^' v":= (g_open 0 (g_var v) G) (at level 30, right associativity).

  Definition unroll G := g_open 0 (g_rec G) G.

  Open Scope fset_scope.

  Lemma in_fold_has (A : choiceType) (x : A) (l : seq {fset A}) :
    (x \in fsetUs l) = has (fun s => x \in s) l.
  Proof.
    rewrite /fsetUs.
    rewrite -[has (fun s => x \in s) l]/(false || has (fun s => x \in s) l).
    rewrite -(in_fset0 x); elim: l fset0.
    + by move=>z; rewrite Bool.orb_false_r.
    + by move=> a l Ih z/=; rewrite Ih in_fsetU orbA.
  Qed.

  Lemma notin_fold_all (A : choiceType) (x : A) (l : seq {fset A}) :
    (x \notin fsetUs l) = all (fun s => x \notin s) l.
  Proof. by rewrite in_fold_has -all_predC. Qed.

  Fixpoint g_fidx (d : nat) (G : g_ty) : {fset nat} :=
    match G with
    | g_var v => if v >= d then [fset v - d] else fset0
    | g_rec G => g_fidx d.+1 G
    | g_msg p q Ks => fsetUs [seq g_fidx d K.cnt | K <- Ks]
    | g_end => fset0
    end.

  Definition g_lc (G : g_ty) := g_fidx 0 G = fset0.

  Definition g_closed (G : g_ty) := g_fidx 0 G == fset0.

  Fixpoint g_free_index (d : nat) (G : g_ty) : seq nat
    :=
    match G with
    | g_end => [::]
    | g_var v => if v >= d then [:: v - d] else [::]
    | g_rec G => g_free_index d.+1 G
    | g_msg p q Ks => flatten [seq g_free_index d K.cnt | K <- Ks]
    end.
  Close Scope fset_scope.

  Lemma gfbvar_next n G :
    g_fidx n G == fset0 ->
    g_fidx n.+1 G = fset0.
  Proof.
    elim/gty_ind1: G n=>[//|v|G Ih|p q Ks Ih] n/=.
    - case: v=>//= m H; case: ifP=>// n_m; move: H.
      by move: (leq_trans (leqnSn n) n_m)=>->; rewrite -cardfs_eq0 cardfs1.
    - by apply: Ih.
    - rewrite fsetUs_fset0 member_map=>H; apply/eqP.
      by rewrite fsetUs_fset0 member_map=> K M; move: (Ih K M n (H K M))=>->.
  Qed.

  Fixpoint guarded d G :=
    match G with
    | g_end
    | g_var _ => true
    | g_rec G => if G is g_var v
                 then v > d
                 else guarded d.+1 G
    | g_msg _ _ Ks => all (fun K => guarded 0 K.cnt) Ks
    end.

  Inductive Guarded : nat -> g_ty -> Prop :=
  | G_end d :
      Guarded d g_end
  | G_var d v :
      Guarded d (g_var v)
  | G_rec_var d v :
      v > d ->
      Guarded d (g_rec (g_var v))
  | G_rec d G :
      (forall v, G != g_var v) ->
      Guarded d.+1 G ->
      Guarded d (g_rec G)
  | G_msg d p q Ks :
      AllGuarded Ks ->
      Guarded d (g_msg p q Ks)
  with AllGuarded : seq (lbl * (mty * g_ty)) -> Prop :=
  | G_nil :
      AllGuarded [::]
  | G_cons K Ks :
      Guarded 0 K.cnt ->
      AllGuarded Ks ->
      AllGuarded (K :: Ks)
  .

  Lemma grec_not_guarded d G' :
    ~ Guarded d.+1 G' ->
    (forall v : nat, G' != g_var v) ->
    ~ Guarded d (g_rec G').
  Proof.
    move=> N_GG' Ne; move: {-1}d (eq_refl d) {-1}(g_rec G') (eq_refl (g_rec G')).
    move=> d' d_d' G Eq_G H; case: H d_d' Eq_G=>//.
    + by move=> d0 v _ _; move: Ne; rewrite !eqE/==>/(_ v)-N E;move:E N=>->.
    + move=> d0 G0 _ GG' /eqP-E1; rewrite !eqE/==>/eqP-E2.
      by move: E1 E2 GG'=><-<-/N_GG'.
  Qed.

  Lemma alt_eq p1 q1 Ks1 p2 q2 Ks2 :
    ((g_msg p1 q1 Ks1) == (g_msg p2 q2 Ks2)) =
    (p1 == p2) && (q1 == q2) && (Ks1 == Ks2).
  Proof.
    rewrite eqE/=; do 2 case: eqP=>//=; move=> _ _ {p1 q1 p2 q2}.
    elim: Ks1=>[|K1 Ks1 Ih] in Ks2 *; case: Ks2=>[|K2 Ks2]//=.
    by rewrite Ih; do ! rewrite !eqE/=; rewrite -!eqE !andbA.
  Qed.

  Lemma gty_not_var A G (f : nat -> A) (k : A) :
    (forall v : nat, G != g_var v) ->
    match G with | g_var v => f v | _ => k end = k.
  Proof. by case: G =>// v /(_ v)/eqP. Qed.

  Lemma guardedP d G : reflect (Guarded d G) (guarded d G).
  Proof.
    move: G d; fix Ih 1; case=> [|v|G|p q Ks] d/=; try do ! constructor.
    - have [[v->]|]: (sig (fun v => G = g_var v) + (forall v, G != g_var v))%type
        by case: G=>[|v||]; try (by right); by (left; exists v).
      * case: (boolP (d < v))=>[d_lt_n|d_ge_n]; do ! constructor =>//.
        move=> GG; case E:_/GG d_ge_n=>[||d' v' H|d' G' H|]//.
        + by move: E H=>[<-] ->.
        + by move: E H=>[<-] /(_ v)/eqP.
      * move=> H; rewrite (gty_not_var _ _ H); case: Ih; do ! constructor=>//.
        move=> GG; case E:_/GG n=>[||d' v' F|d' G' _ F|]//.
        + by move: E H=>[->] /(_ v')/eqP.
        + by move: E F=>[->] F /(_ F).
    - elim: Ks=>[|K Ks]//=; try do ! constructor=>//.
      case: (Ih K.cnt 0)=>[GK [GG|N_GG]|N_GK]/=; do ! constructor=>//.
      * case Eq: (g_msg p q Ks) / GG=>// [d' p' q' Ks' GKs].
        move: Eq=>/eqP; rewrite alt_eq =>/andP-[_ Eq].
        by move: Eq GKs=>/eqP<-.
      * move=> NGG; case Eq: (g_msg _ _ _) / NGG=>// [d' p' q' Ks' GKs].
        move: Eq=>/eqP; rewrite alt_eq =>/andP-[_ Eq].
        move: Eq GKs=>/eqP<- H; case Eq: (K::Ks) / H =>// [K' Ks'' _ GKs].
        by move: Eq GKs=>[_ <-] /(G_msg d p q)/N_GG.
      * move=> NGG; case Eq: (g_msg _ _ _) / NGG=>// [d' p' q' Ks' GKs].
        move: Eq=>/eqP; rewrite alt_eq =>/andP-[_ Eq].
        move: Eq GKs=>/eqP<-H'; case Eq: (K::Ks) / H' =>// [K' Ks'' GK0 _].
        by move: Eq GK0=>[<- _] /N_GK.
  Qed.

  Fixpoint rec_depth G :=
    match G with
    | g_rec G => (rec_depth G).+1
    | _ => 0
    end.

  Fixpoint n_unroll d G :=
    match d with
    | 0 => G
    | d.+1 =>
      match G with
      | g_rec G' => n_unroll d (unroll G')
      | _ => G
      end
    end.

  Lemma guarded_match d G :
    match G with
    | g_var v => d < v
    | _ => guarded d.+1 G
    end ->
    (exists v, (G == g_var v) && (d < v)) \/
    (forall v, (G != g_var v)) /\ guarded d.+1 G.
  Proof.
    case: G=>[|[]||]//=; try by right.
    by move=> n d_n; left; exists n.+1; rewrite eq_refl.
  Qed.

  Lemma guarded_recdepth d G m :
    (forall v : nat, G != g_var v) ->
    guarded d G ->
    m < d ->
    forall G', rec_depth G = rec_depth ({m ~> G'} G).
  Proof.
    elim/gty_ind1: G=>[|n|G Ih|p q Ks Ih]//= in d m *.
    - by move=>/(_ n)/eqP.
    - move=> _ /guarded_match-[[n /andP-[/eqP->]/=]|[]].
      + move=> dn md G'; move: dn md; case: ifP=>[/eqP-> d_lt_n n_le_d|//].
        by move: (leq_trans d_lt_n n_le_d); rewrite ltnn.
      + move=>/(Ih d.+1)-{Ih}Ih /Ih-{Ih}Ih m_le_d G'.
        by rewrite -Ih.
  Qed.

  Lemma guarded_depth_gt dG dG' G :
    guarded dG' G -> g_closed G -> guarded dG G.
  Proof.
    rewrite /g_closed=> H H'; move: 0 (leq0n dG') H H'.
    elim/gty_ind1: G =>[|[a|n]|G Ih|p q Ks Ih]// in dG dG' *.
    move=> n n_le_dG'.
    move=>/guarded_match-[[m /andP-[/eqP->]]|[]].
    - rewrite /=; case: ifP=>//=.
      + by rewrite -cardfs_eq0 cardfs1.
      + move=>/(rwP negPf); rewrite -leqNgt => m_leq_n dG'_le_m.
        by move: (leq_ltn_trans n_le_dG' dG'_le_m); rewrite ltnNge m_leq_n.
    - by move=>/(gty_not_var _ _)/=->; apply: Ih.
  Qed.

  Lemma gopen_closed G :
     g_closed (g_rec G) ->
     g_closed (g_open 0 (g_rec G) G).
   Proof.
     rewrite/g_closed/==>G_fbv; have: g_fidx 0 (g_rec G) == fset0 by [].
     move: (g_rec G) => G' G'0.
     elim/gty_ind1: G 0 G'0 G_fbv=>[//|v|G Ih|p q Ks Ih] n G'0/=.
     - move=> H; case: ifP=>[//|/=]; case: ifP=>//; move: H.
       case: ifP=>//; first by rewrite -cardfs_eq0 cardfs1//.
       rewrite ltn_neqAle =>/(rwP negPf); rewrite negb_and negbK eq_sym.
       by move=>/orP-[->//|/negPf->].
     - by apply: (Ih n.+1); rewrite gfbvar_next.
     - rewrite -map_comp/comp/=; move=>/fsetUs_fset0/member_map-H.
       by apply/fsetUs_fset0/member_map=>K M; apply: Ih=>//; apply: H.
   Qed.

  Lemma closed_not_var G :
    g_closed G ->
    forall v, G != g_var v.
  Proof.
    by rewrite /g_closed; case: G=>//= n; rewrite -cardfs_eq0 cardfs1.
  Qed.

  Lemma open_not_var d G G' :
    g_closed G ->
    (forall v, G' != g_var v) ->
    forall v, {d ~> G} G' != g_var v.
  Proof. by case: G'=>// n _ /(_ n)/eqP. Qed.

  Lemma guarded_open d1 d2 G G' :
    guarded 0 G' ->
    g_closed G' ->
    guarded d1 G ->
    guarded d1 ({d2 ~> G'} G).
  Proof.
    elim/gty_ind1: G=>[|n|G Ih|p q Ks Ih]//= in d1 d2 *.
    - by case: ifP=>// _ /guarded_depth_gt-H /H-{H}H.
    - move=>GG' CG'.
      move=> /guarded_match-[[v /andP-[/eqP-EG]]/=|[]].
      + move: EG=>->/=; case: ifP=>[/eqP _ _|//].
        rewrite (gty_not_var _ _ (closed_not_var CG')).
        by apply/(guarded_depth_gt _ GG' CG').
      + move=> H; move: (open_not_var d2.+1 CG' H)=>/(gty_not_var _ _)->.
        by apply/Ih.
    - move=> GG' CG'; elim: Ks=>[|K Ks IhK]//= in Ih *.
      move=>/andP-[GK GKs].
      move: (Ih K (or_introl (erefl _)) 0 d2 GG' CG' GK)=>->//=.
      apply/IhK=>// K0 MK0; by apply/(Ih K0 (or_intror MK0)).
  Qed.

  Lemma guarded_gt d d' G :
    d > d' ->
    guarded d G ->
    guarded d' G.
  Proof.
    elim/gty_ind1: G=>[|[a|n]|G Ih|p q Ks Ih]//= in d d' *.
    move=> d'_lt_d /guarded_match-[[v /andP-[/eqP->]]|[]].
    - by move=>/(ltn_trans d'_lt_d).
    - by move/(gty_not_var _ _)=>->; apply: Ih.
  Qed.

  Lemma unroll_guarded G :
    g_closed G ->
    guarded 0 G ->
    forall G', n_unroll (rec_depth G) G != g_rec G'.
  Proof.
    move: {-2}(rec_depth G) (eq_refl (rec_depth G)) => n.
    elim: n => [|n Ih]/= in G *; case: G=>// G n_rd CG GG; move: n_rd.
    rewrite eqE/=-eqE => n_rd.
    have: (guarded 0 (g_rec G)) by [].
    move=> /guarded_match-[[x /andP-[/eqP-G_v x_ne0]]|].
    - move: G_v n_rd=>-> /eqP->/= G'; rewrite /unroll/=.
      by move: x_ne0; case: ifP=>[/eqP->|].
    - move=>[G_ne_bv GG']; move: n_rd.
      rewrite (guarded_recdepth G_ne_bv GG' (ltn0Sn 0) (g_rec G)) =>n_rd.
      apply/Ih=>//; first by apply/gopen_closed.
      by move: (guarded_open 0 GG CG GG')=>/guarded_gt-H; apply/H.
  Qed.

  Close Scope mpst_scope.
End Syntax.

Section Semantics.

  Open Scope mpst_scope.
  CoInductive rg_ty :=
  | rg_end
  | rg_msg (ST : option lbl)
           (FROM TO : role)
           (CONT : lbl /-> mty * rg_ty).

  Inductive g_unroll (r : rel2 g_ty (fun=>rg_ty)) : rel2 g_ty (fun=>rg_ty) :=
  | gu_end : @g_unroll r g_end rg_end
  | gu_rec IG CG : r (g_open 0 (g_rec IG) IG) CG -> @g_unroll r (g_rec IG) CG
  | gu_msg FROM TO iCONT cCONT :
      @unroll_all r iCONT cCONT ->
      @g_unroll r (g_msg FROM TO iCONT) (rg_msg None FROM TO cCONT)
  with unroll_all (r : rel2 g_ty (fun=>rg_ty))
       : rel2 (seq (lbl * (mty * g_ty))) (fun=>lbl /-> mty * rg_ty) :=
  | gu_nil : @unroll_all r [::] (empty _)
  | gu_cons L T IG CG iCONT cCONT :
      r IG CG ->
      @unroll_all r iCONT cCONT ->
      @unroll_all r ((L, (T, IG)) :: iCONT) (extend L (T, CG) cCONT).
  Definition GUnroll IG CG : Prop := paco2 g_unroll bot2 IG CG.
  Hint Constructors g_unroll.
  Hint Constructors unroll_all.

  Lemma gunroll_monotone : monotone2 g_unroll.
  Proof.
    move=> IG CG r r' U H; move: IG CG U.
    elim/gty_ind1=>[|V|G IH|F T C IH] CG;
      case E:_ _/ =>[|G' CG' R|F' T' C' CC U]//.
    - by move: E R=>[<-]{G'} /H; constructor.
    - move: E U=>[<-<-<-]{F' T' C'} U; constructor; move: U IH.
      elim=>[|L Ty IG CG' iCONT cCONT /H-R U /=IH1 IH2]; constructor=>//.
      by apply/IH1=> K M; apply/IH2; right.
  Qed.
  Hint Resolve gunroll_monotone.

  Lemma gunroll_unfold iG cG
    : GUnroll iG cG -> @g_unroll (upaco2 g_unroll bot2) iG cG.
  Proof. by move/(paco2_unfold gunroll_monotone). Qed.

  Lemma GUnroll_ind n iG cG :
    GUnroll iG cG <-> GUnroll (n_unroll n iG) cG.
  Proof.
    split.
    - elim: n =>// n Ih in iG cG *.
      move=> /gunroll_unfold-[]//=.
      + by apply/paco2_fold.
      + by move=>IG CG [/Ih|].
      + by move=>F T IC CC /(gu_msg F T)-H; apply/paco2_fold.
    - elim: n =>// n Ih in iG cG *.
      by case: iG=>//= G H1; apply/paco2_fold; constructor; left; apply/Ih.
  Qed.

  Definition R_only (R : rel2 rg_ty (fun=>rg_ty))
             L0 (C C' : lbl /-> mty * rg_ty) :=
    (forall L1 K, L0 != L1 -> C L1 = Some K <-> C' L1 = Some K)
    /\ exists Ty G0 G1,
      C L0 = Some (Ty, G0)
      /\ C' L0 = Some (Ty, G1)
      /\ R G0 G1.

  Inductive step : act -> rg_ty -> rg_ty -> Prop :=
  (* Basic rules *)
  | st_send L F T C Ty G :
      C L = Some (Ty, G) ->
      step (a_send F T L Ty) (rg_msg None F T C) (rg_msg (Some L) F T C)
  | st_recv L F T C Ty G :
      C L = Some (Ty, G) ->
      step (a_recv F T L Ty) (rg_msg (Some L) F T C) G
  (* Struct *)
  | st_amsg1 a F T C0 C1 :
      subject a != F ->
      subject a != T ->
      same_dom C0 C1 ->
      R_all (step a) C0 C1 ->
      step a (rg_msg None F T C0) (rg_msg None F T C1)
  | st_amsg2 a L F T C0 C1 :
      subject a != T ->
      same_dom C0 C1 ->
      R_only (step a) L C0 C1 ->
      step a (rg_msg (Some L) F T C0) (rg_msg (Some L) F T C1)
  .

  Derive Inversion step_inv with (forall a G G', step a G G') Sort Prop.

  Scheme step_ind1 := Induction for step Sort Prop.

  Inductive g_lts_ (r : rel2 trace (fun=>rg_ty)) : rel2 trace (fun=>rg_ty) :=
  | eg_end : @g_lts_ r tr_end rg_end
  | eg_trans a t G G' :
      step a G G' ->
      r t G' ->
      @g_lts_ r (tr_next a t) G.
  Hint Constructors g_lts_.
  Definition g_lts t g := paco2 g_lts_ bot2 t g.

  Lemma g_lts_monotone : monotone2 g_lts_.
  Proof. pmonauto. Qed.
  Hint Resolve g_lts_monotone.

  Close Scope mpst_scope.

End Semantics.
