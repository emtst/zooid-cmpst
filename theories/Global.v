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
  Unset Elimination Schemes.
  (**
   * Global Types
   *)
  Inductive g_ty :=
  | g_end
  | g_var (VAR : nat)
  | g_rec (GT : g_ty)
  | g_msg (FROM TO : role) (CONT : seq (lbl * (mty * g_ty))).
  Hint Constructors g_ty : mpst.

  Set Elimination Schemes.

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

  Lemma g_ty_ind :
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
  Qed.
  Hint Rewrite eqgty_all : mpst.

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

  Lemma rec_gty G :
    (exists G', G = g_rec G') \/ (forall G', G != g_rec G').
  Proof. by case:G; try (by right); move=> GT; left; exists GT. Qed.

  Lemma matchGrec A G (f : g_ty -> A) g :
    (forall G', G != g_rec G') ->
    match G with
    | g_rec G' => f G'
    | _ => g
    end = g.
  Proof. by case: G=>// GT /(_ GT)/eqP. Qed.

  (**
   * Does not apply any "shift" to G2, and therefore G2 must always be closed
   *)
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

  Lemma g_open_msg_rw d G2 FROM TO CONT:
    g_open d G2 (g_msg FROM TO CONT)
    = g_msg FROM TO [seq (K.lbl, (K.mty, g_open d G2 K.cnt)) | K <- CONT].
  Proof. by []. Qed.

  Lemma notin_part_g_open_strong d r G G': r \notin participants G ->
    r \notin participants G'-> r \notin participants (g_open d G' G).
  Proof.
  move=> h1 rnG'; move: h1; apply: contra; elim: G d.
  + rewrite //=.
  + rewrite //= => v d.
    by case: ifP=>[_ F|//]; rewrite F in rnG'.
  + rewrite //=. by move=> G ih d; apply ih.
  + move=>p q Ks ih d. rewrite /= !in_cons -map_comp/comp/=.
    move=>/orP-[->//|/orP-[->|]]; first by rewrite orbC.
    move=> H.
    do ! (apply/orP; right).
    move: H=>/flatten_mapP-[K inKs inK].
    apply/flatten_mapP.
    exists K=>//.
    by apply: (ih _ _ d); first by apply/memberP.
  Qed.

  Lemma same_notin_part_g_open d r G G': participants G' = participants G ->
    r \notin participants G -> r \notin participants (g_open d G' G).
  Proof.
  move=> hp1 hp2; apply: notin_part_g_open_strong; [by apply hp2 | by rewrite hp1 //=].
  Qed.

  Lemma notin_part_g_open r G:
    r \notin participants G -> r \notin participants (g_open 0 (g_rec G) G).
  Proof.
  by apply same_notin_part_g_open; rewrite //=.
  Qed.

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
  Hint Rewrite in_fold_has : mpst.

  Lemma notin_fold_all (A : choiceType) (x : A) (l : seq {fset A}) :
    (x \notin fsetUs l) = all (fun s => x \notin s) l.
  Proof. by rewrite in_fold_has -all_predC. Qed.
  Hint Rewrite notin_fold_all: mpst.

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
    elim: G n=>[//|v|G Ih|p q Ks Ih] n/=.
    - case: v=>//= m H; case: ifP=>// n_m; move: H.
      by move: (leq_trans (leqnSn n) n_m)=>->; rewrite -cardfs_eq0 cardfs1.
    - by apply: Ih.
    - rewrite fsetUs_fset0 member_map=>H; apply/eqP.
      by rewrite fsetUs_fset0 member_map=> K M; move: (Ih K M n (H K M))=>->.
  Qed.

  Fixpoint guarded d G :=
    match G with
    | g_end => true
    | g_var v => v >= d
    | g_rec G => guarded d.+1 G
    | g_msg _ _ Ks => all (fun K => guarded 0 K.cnt) Ks
    end.

  Fixpoint g_binds n G :=
    match G with
    | g_var v => v == n
    | g_rec G => g_binds n.+1 G
    | _ => false
    end.

  Fixpoint guarded' G :=
    match G with
    | g_end
    | g_var _ => true
    | g_rec G => ~~ g_binds 0 G && guarded' G
    | g_msg _ _ Ks => all (fun K => guarded' K.cnt) Ks
    end.

  Lemma guarded_next n G : guarded n.+1 G = ~~ g_binds n G && guarded n G.
  Proof. by elim: G n=>//= v n; rewrite ltn_neqAle eq_sym. Qed.

  Lemma guarded_binds G : guarded 0 G = guarded' G.
  Proof.
    elim: G=>[||G|_ _ Ks Ih]//=; first by move=><-;apply/guarded_next.
    elim: Ks Ih=>[//|K Ks Ih']/= Ih; rewrite Ih; last by left.
    by rewrite Ih' // => K' /or_intror/Ih.
  Qed.

  (* Inductive Guarded : nat -> g_ty -> Prop := *)
  (* | G_end d : *)
  (*     Guarded d g_end *)
  (* | G_var d v : *)
  (*     v >= d -> *)
  (*     Guarded d (g_var v) *)
  (* | G_rec d G : *)
  (*     Guarded d.+1 G -> *)
  (*     Guarded d (g_rec G) *)
  (* | G_msg d p q Ks : *)
  (*     AllGuarded Ks -> *)
  (*     Guarded d (g_msg p q Ks) *)
  (* with AllGuarded : seq (lbl * (mty * g_ty)) -> Prop := *)
  (* | G_nil : *)
  (*     AllGuarded [::] *)
  (* | G_cons K Ks : *)
  (*     Guarded 0 K.cnt -> *)
  (*     AllGuarded Ks -> *)
  (*     AllGuarded (K :: Ks) *)
  (* . *)

  (* Lemma grec_not_guarded d G' : *)
  (*   ~ Guarded d.+1 G' -> *)
  (*   (forall v : nat, G' != g_var v) -> *)
  (*   ~ Guarded d (g_rec G'). *)
  (* Proof. *)
  (*   move=> N_GG' Ne; move: {-1}d (eq_refl d) {-1}(g_rec G') (eq_refl (g_rec G')). *)
  (*   move=> d' d_d' G Eq_G H; case: H d_d' Eq_G=>//. *)
  (*   + by move=> d0 v _ _; move: Ne; rewrite !eqE/==>/(_ v)-N E;move:E N=>->. *)
  (*   + move=> d0 G0 _ GG' /eqP-E1; rewrite !eqE/==>/eqP-E2. *)
  (*     by move: E1 E2 GG'=><-<-/N_GG'. *)
  (* Qed. *)

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

  (* Lemma guardedP d G : reflect (Guarded d G) (guarded d G). *)
  (* Proof. *)
  (*   move: G d; fix Ih 1; case=> [|v|G|p q Ks] d/=; try do ! constructor. *)
  (*   - case: (boolP (d <= v)); do ! constructor=>//. *)
  (*     move=> H; move: H i; case E: _ / =>[|v' v'' H||]//. *)
  (*     by move: E H=>[<-]->. *)
  (*   - case: Ih; do ! constructor=>//. *)
  (*   - have [[v->]|]: (sig (fun v => G = g_var v) + (forall v, G != g_var v))%type *)
  (*       by case: G=>[|v||]; try (by right); by (left; exists v). *)
  (*     * case: (boolP (d < v))=>[d_lt_n|d_ge_n]; do ! constructor =>//. *)
  (*       move=> GG; case E:_/GG d_ge_n=>[||d' v' H|d' G' H|]//. *)
  (*       + by move: E H=>[<-] ->. *)
  (*       + by move: E H=>[<-] /(_ v)/eqP. *)
  (*     * move=> H; rewrite (gty_not_var _ _ H); case: Ih; do ! constructor=>//. *)
  (*       move=> GG; case E:_/GG n=>[||d' v' F|d' G' _ F|]//. *)
  (*       + by move: E H=>[->] /(_ v')/eqP. *)
  (*       + by move: E F=>[->] F /(_ F). *)
  (*   - elim: Ks=>[|K Ks]//=; try do ! constructor=>//. *)
  (*     case: (Ih K.cnt 0)=>[GK [GG|N_GG]|N_GK]/=; do ! constructor=>//. *)
  (*     * case Eq: (g_msg p q Ks) / GG=>// [d' p' q' Ks' GKs]. *)
  (*       move: Eq=>/eqP; rewrite alt_eq =>/andP-[_ Eq]. *)
  (*       by move: Eq GKs=>/eqP<-. *)
  (*     * move=> NGG; case Eq: (g_msg _ _ _) / NGG=>// [d' p' q' Ks' GKs]. *)
  (*       move: Eq=>/eqP; rewrite alt_eq =>/andP-[_ Eq]. *)
  (*       move: Eq GKs=>/eqP<- H; case Eq: (K::Ks) / H =>// [K' Ks'' _ GKs]. *)
  (*       by move: Eq GKs=>[_ <-] /(G_msg d p q)/N_GG. *)
  (*     * move=> NGG; case Eq: (g_msg _ _ _) / NGG=>// [d' p' q' Ks' GKs]. *)
  (*       move: Eq=>/eqP; rewrite alt_eq =>/andP-[_ Eq]. *)
  (*       move: Eq GKs=>/eqP<-H'; case Eq: (K::Ks) / H' =>// [K' Ks'' GK0 _]. *)
  (*       by move: Eq GK0=>[<- _] /N_GK. *)
  (* Qed. *)

  Fixpoint rec_depth G :=
    match G with
    | g_rec G => (rec_depth G).+1
    | _ => 0
    end.


  Lemma rd_zero G :
    (forall G' : g_ty, G != g_rec G') ->
    rec_depth G = 0.
  Proof. by case: G=>// GT /(_ GT)/eqP. Qed.


  Fixpoint n_unroll d G :=
    match d with
    | 0 => G
    | d.+1 =>
      match G with
      | g_rec G' => n_unroll d (unroll G')
      | _ => G
      end
    end.


  Lemma r_in_unroll r G n:
    r \in participants (n_unroll n G) -> r \in participants G.
  Proof.
  apply: contraLR.
  elim: n => [rewrite //= | n ih] in G *; case G; rewrite //=.
  move=> G0 notinpart; apply ih.
  unfold unroll; apply notin_part_g_open; by [].
  Qed.

  Lemma r_in_unroll_rec_depth r G:
    r \in participants (n_unroll (rec_depth G) G) -> r \in participants G.
  Proof. by apply r_in_unroll. Qed.

  Lemma notin_nunroll r n G :
    r \notin participants G ->
    r \notin participants (n_unroll n G).
  Proof.
    elim: n G=>//= n Ih G H.
    by case: G H=>//= GT; rewrite /unroll=>/notin_part_g_open/Ih.
  Qed.

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
    guarded d G ->
    m < d ->
    forall G', rec_depth G = rec_depth ({m ~> G'} G).
  Proof.
    elim: G=>[|n|G Ih|p q Ks Ih]//= in d m *.
    - move=>dn md G; case: ifP=>[/eqP-E|ne//].
      by move: E dn md=>-> /leq_ltn_trans-H /H; rewrite ltnn.
    - by move=> GG md G'; rewrite (Ih _ m.+1 GG _ G').
  Qed.

  Lemma guarded_depth_gt n dG dG' G :
    n <= dG' ->
    guarded dG' G -> g_fidx n G == fset0 -> guarded dG G.
  Proof.
    elim: G =>[|m|G Ih|p q Ks Ih]// in n dG dG' *.
    - by move=> /leq_trans-H /= /H->; rewrite -cardfs_eq0 cardfs1.
    - by move=>/= LE; apply/Ih.
  Qed.

  Lemma gopen_closed G :
     g_closed (g_rec G) ->
     g_closed (g_open 0 (g_rec G) G).
   Proof.
     rewrite/g_closed/==>G_fbv; have: g_fidx 0 (g_rec G) == fset0 by [].
     move: (g_rec G) => G' G'0.
     elim: G 0 G'0 G_fbv=>[//|v|G Ih|p q Ks Ih] n G'0/=.
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
    elim: G=>[|n|G Ih|p q Ks Ih]//= in d1 d2 *.
    - by case: ifP=>// _ /(guarded_depth_gt d1 (leq0n 0))-H /H-{H}H.
    - by apply/Ih.
    - move=> GG' CG'; elim: Ks=>[|K Ks IhK]//= in Ih *.
      move=>/andP-[GK GKs].
      move: (Ih K (or_introl (erefl _)) 0 d2 GG' CG' GK)=>->//=.
      apply/IhK=>// K0 MK0; by apply/(Ih K0 (or_intror MK0)).
  Qed.

  Lemma guarded_gt d d' G :
    d >= d' ->
    guarded d G ->
    guarded d' G.
  Proof.
    elim: G=>[|n|G Ih|p q Ks Ih]//= in d d' *.
    - by move=>/leq_trans-H /H.
    - by move=> H; apply/Ih.
  Qed.

  Lemma unroll_guarded G :
    g_closed G ->
    guarded 0 G ->
    forall G', n_unroll (rec_depth G) G != g_rec G'.
  Proof.
    move: {-2}(rec_depth G) (eq_refl (rec_depth G)) => n.
    elim: n => [|n Ih]/= in G *; case: G=>// G n_rd CG GG; move: n_rd.
    rewrite eqE/=-eqE => n_rd.
    have/=GG': (guarded 0 (g_rec G)) by [].
    move: n_rd; rewrite (guarded_recdepth GG' (ltn0Sn 0) (g_rec G))=>n_rd.
    apply/Ih=>//; first by apply/gopen_closed.
    by apply/guarded_open=>//; apply/guarded_gt; last by apply/GG'.
  Qed.

  Close Scope mpst_scope.
End Syntax.

Section Semantics.

  Open Scope mpst_scope.
  CoInductive rg_ty :=
  | rg_end
  | rg_msg (FROM TO : role)
           (CONT : lbl /-> mty * rg_ty).

  Unset Elimination Schemes.
  Inductive ig_ty :=
  | ig_end (CONT : rg_ty)
  | ig_msg (ST : option lbl)
           (FROM TO : role)
           (CONT : lbl /-> mty * ig_ty).
  Set Elimination Schemes.

  Inductive part_of: role -> rg_ty -> Prop :=
    | pof_from F T C: part_of F (rg_msg F T C)
    | pof_to F T C: part_of T (rg_msg F T C)
    | pof_cont p F T C L G Ty: C L = Some (Ty, G)
      -> part_of p G -> part_of p (rg_msg F T C).

  Inductive part_of_all: role -> rg_ty -> Prop :=
    | pall_from F T C: part_of_all F (rg_msg F T C)
    | pall_to F T C: part_of_all T (rg_msg F T C)
    | pall_cont p F T C :
        P_all (part_of_all p) C -> part_of_all p (rg_msg F T C).

  (* Needed to build the next global type in a step  *)
  Inductive part_of_allT: role -> rg_ty -> Type :=
    | pallT_from F T C: part_of_allT F (rg_msg F T C)
    | pallT_to F T C: part_of_allT T (rg_msg F T C)
    | pallT_cont p F T C :
        (forall l Ty G, C l = Some (Ty, G) -> part_of_allT p G) ->
        part_of_allT p (rg_msg F T C).

  Inductive iPart_of: role -> ig_ty -> Prop :=
    | ipof_end p cG: part_of p cG -> iPart_of p (ig_end cG)
    | ipof_from F T C: iPart_of F (ig_msg None F T C)
    | ipof_to o F T C: iPart_of T (ig_msg o F T C)
    | ipof_cont p o F T C L G Ty: C L = Some (Ty, G)
      -> iPart_of p G -> iPart_of p (ig_msg o F T C).

  Lemma rgend_part p G : part_of_all p G -> G = rg_end -> False.
  Proof. by move=>[]. Qed.

  Lemma pall_inv F T C G p :
    part_of_all p G -> G = rg_msg F T C -> F <> p -> T <> p ->
    (forall l Ty G, C l = Some (Ty, G) -> part_of_all p G).
  Proof.
      by move=>[ F' T' C' [->]//
               | F' T' C' [_ ->]//
               |{}p F' T' C' ALL [_ _ <-] _ _ l Ty {}G /ALL
               ].
  Defined.

  Fixpoint find_partsc p G (H : part_of_all p G) {struct H}
    : part_of_allT p G
    :=
    match G as G0 return G = G0 -> part_of_allT p G0 with
    | rg_msg F T C => fun EQ =>
                        match @eqP role F p with
                        | ReflectT pF => match EQ, pF with
                                         | erefl, erefl => pallT_from F T C
                                         end
                        | ReflectF pF =>
                          match @eqP role T p with
                          | ReflectT pT => match EQ, pT with
                                           | erefl, erefl => pallT_to F T C
                                           end
                          | ReflectF pT =>
                            pallT_cont F T
                                       (fun l Ty G Cl =>
                                          find_partsc (pall_inv H EQ pF pT Cl))
                          end
                        end
    | rg_end => fun E => match rgend_part H E with end
    end erefl.

  Definition rg_unr (G : rg_ty) : ig_ty :=
    match G with
    | rg_msg F T C
        => ig_msg None F T
                  (fun lbl =>
                    match C lbl with
                    | None => None
                    | Some (t, G) => Some (t, ig_end G)
                    end)
    | rg_end => ig_end rg_end
    end.

  Definition P_option A (P : A -> Type) (C : option A) : Type :=
    match C with
    | Some X => P X
    | None => True
    end.

  Definition P_prod A B (P : B -> Type) (C : A * B) : Type :=
    match C with
    | (X, Y)=> P Y
    end.

  Lemma ig_ty_ind'
    (P : ig_ty -> Prop)
    (P_end : forall CONT, P (ig_end CONT))
    (P_msg : (forall ST FROM TO CONT,
      (forall L, P_option (P_prod P) (CONT L)) ->
      P (ig_msg ST FROM TO CONT)))
  : forall G, P G.
  Proof.
    fix Ih 1; case.
    - by apply: P_end.
    - move=> ST F T C; apply: P_msg => L.
      case: (C L)=>[[Ty G]|].
      + by rewrite /P_option/P_prod; apply/Ih.
      + by rewrite /P_option.
  Qed.

  Lemma ig_ty_ind
    (P : ig_ty -> Prop)
    (P_end : forall CONT, P (ig_end CONT))
    (P_msg : (forall ST FROM TO CONT,
      (forall L Ty G, CONT L = Some (Ty, G) -> P G) ->
      P (ig_msg ST FROM TO CONT)))
  : forall G, P G.
  Proof.
    elim/ig_ty_ind'=>// ST FROM TO CONT Ih.
    apply/P_msg => L Ty G; move: (Ih L); case: (CONT L) =>[[Ty' G']|]//=.
    by move=> P_G' [_ <-].
  Qed.

  Lemma ig_ty_rect'
    (P : ig_ty -> Type)
    (P_end : forall CONT, P (ig_end CONT))
    (P_msg : (forall ST FROM TO CONT,
      (forall L, P_option (P_prod P) (CONT L)) ->
      P (ig_msg ST FROM TO CONT)))
  : forall G, P G.
  Proof.
    fix Ih 1; case.
    - by apply: P_end.
    - move=> ST F T C; apply: P_msg => L.
      case: (C L)=>[[Ty G]|].
      + by rewrite /P_option/P_prod; apply/Ih.
      + by rewrite /P_option.
  Qed.

  Lemma ig_ty_rect
    (P : ig_ty -> Type)
    (P_end : forall CONT, P (ig_end CONT))
    (P_msg : (forall ST FROM TO CONT,
      (forall L Ty G, CONT L = Some (Ty, G) -> P G) ->
      P (ig_msg ST FROM TO CONT)))
  : forall G, P G.
  Proof.
    elim/ig_ty_rect'=>// ST FROM TO CONT Ih.
    apply/P_msg => L Ty G; move: (Ih L); case: (CONT L) =>[[Ty' G']|]//=.
    by move=> P_G' [_ <-].
  Qed.

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

  Fixpoint non_empty_cont G :=
    match G with
    | g_msg _ _ Ks => ~~ nilp Ks && all id [seq non_empty_cont K.cnt | K <- Ks]
    | g_rec G => non_empty_cont G
    | _ => true
    end.

  Definition g_precond G :=
    g_closed G && guarded 0 G && non_empty_cont G.

  Lemma ne_open n G G' :
    non_empty_cont G -> non_empty_cont G' -> non_empty_cont (g_open n G' G).
  Proof.
    move=> NE1 NE2; move: NE1.
    elim: G n=>//.
    - by move=>v n; rewrite /unroll/=; case: ifP=>//.
    - by move=> G Ih n /=; apply/Ih.
    - move=> F T C Ih n /=; case: C Ih=>//= K Ks Ih /andP-[NE_K ALL].
      rewrite (Ih K (or_introl erefl) n NE_K) /= {NE_K}.
      move: Ih=>/(_ _ (or_intror _) n)=> Ih.
      move: ALL=>/forallbP/forall_member/member_map-ALL.
      apply/forallbP/forall_member/member_map/member_map=>/={}K M.
      by apply/(Ih _ M)/ALL.
  Qed.

  Lemma ne_unr n G : non_empty_cont G -> non_empty_cont (n_unroll n G).
  Proof.
    elim: n G=>[//|n/=] Ih; case=>//= G NE.
    have: non_empty_cont (g_rec G) by [].
    by move=>/(ne_open 0 NE); apply/Ih.
  Qed.

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
        move: cG; rewrite /g_closed/==>/fsetUs_fset0/member_map-cG.
        move: gG; rewrite /==>/forallbP/forall_member-gG.
        move: NE=>/==>/andP-[NE_C]/forallbP/forall_member/member_map-NE.
        move: (find_member FND)=>MEM.
        rewrite g_expand_once.
        by apply/(CIH _ (gG _ MEM) (cG _ MEM) (NE _ MEM)).
  Qed.

  Definition R_only (R : ig_ty -> ig_ty -> Prop)
             L0 (C C' : lbl /-> mty * ig_ty) :=
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

  Close Scope mpst_scope.

End Semantics.
