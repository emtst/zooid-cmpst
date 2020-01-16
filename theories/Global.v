From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.
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
  | g_var (v : nat)
  | g_rec (G : g_ty)
  | g_msg (p : role) (q : role) (Ks : seq (lbl * (mty * g_ty))).

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

  CoInductive rg_ty :=
  | rg_end
  | rg_msg (a : option lbl) (p : role) (q : role) (Ks : seq (lbl * (mty * rg_ty))).

  CoInductive GUnroll : g_ty -> rg_ty -> Prop :=
  | gu_end : GUnroll g_end rg_end
  | gu_rec G G' : GUnroll (g_open 0 (g_rec G) G) G' -> GUnroll (g_rec G) G'
  | gu_msg p q Ks Ks' : GUnrollAll Ks Ks' ->
                        GUnroll (g_msg p q Ks) (rg_msg None p q Ks')
  with GUnrollAll
       : seq (lbl * (mty * g_ty)) -> seq (lbl * (mty * rg_ty)) -> Prop :=
  | gu_nil : GUnrollAll [::] [::]
  | gu_cons l t G G' Ks Ks' :
      GUnroll G G' ->
      GUnrollAll Ks Ks' ->
      GUnrollAll ((l, (t, G)) :: Ks) ((l, (t, G')) :: Ks')
  .
  Open Scope mpst_scope.

  Lemma GUnroll_ind n iG cG :
    GUnroll iG cG <-> GUnroll (n_unroll n iG) cG.
  Proof.
    split.
    - elim: n =>// n Ih in iG cG *; case=>/=; try by constructor.
      move=> iG' cG'; by apply: Ih.
    - elim: n =>// n Ih in iG cG *.
      by case: iG=>//= G H1; constructor; move: H1; apply/Ih.
  Qed.

  Inductive step : act -> rg_ty -> rg_ty -> Prop :=
  (* Basic rules *)
  | st_send lb p q Ks t G :
      lookup lb Ks = Some (t, G) ->
      step (a_send p q lb t) (rg_msg None p q Ks) (rg_msg (Some lb) p q Ks)
  | st_recv lb p q Ks t G :
      lookup lb Ks = Some (t, G) ->
      step (a_recv p q lb t) (rg_msg (Some lb) p q Ks) G
  (* Struct *)
  | st_amsg1 a p q Ks Ks' :
      subject a != p ->
      subject a != q ->
      step_all a Ks Ks' ->
      step a (rg_msg None p q Ks) (rg_msg None p q Ks')
  | st_amsg2 l a p q Ks Ks' :
      subject a != q ->
      step_only l a Ks Ks' ->
      step a (rg_msg (Some l) p q Ks) (rg_msg (Some l) p q Ks')
  with
  step_all : act ->
             seq (lbl * (mty * rg_ty)) ->
             seq (lbl * (mty * rg_ty)) ->
             Prop :=
  | step_a1 a : step_all a [::] [::]
  | step_a2 a G G' Ks Ks' l t :
      step a G G' ->
      step_all a Ks Ks' ->
      step_all a ((l, (t, G)) :: Ks) ((l, (t, G')) :: Ks')
  with
  step_only : lbl ->
              act ->
              seq (lbl * (mty * rg_ty)) ->
              seq (lbl * (mty * rg_ty)) ->
              Prop :=
  | step_o1 l a G G' t Ks :
      step a G G' ->
      step_only l a ((l, (t, G)) :: Ks) ((l, (t, G')) :: Ks)
  | step_o2  l a Ks Ks' K :
      l != K.lbl ->
      step_only l a Ks Ks' ->
      step_only l a (K :: Ks) (K :: Ks')
  .

  Derive Inversion step_inv with (forall a G G', step a G G') Sort Prop.

  Scheme step_ind1 := Induction for step Sort Prop
  with stepall_ind1 := Induction for step_all Sort Prop
  with steponly_ind1 := Induction for step_only Sort Prop.

  CoInductive g_lts : trace -> rg_ty -> Prop :=
  | eg_end : g_lts tr_end rg_end
  | eg_trans a t G G' :
      step a G G' ->
      g_lts t G' ->
      g_lts (tr_next a t) G.

  Derive Inversion glts_inv with (forall tr G, g_lts tr G) Sort Prop.

End Semantics.
