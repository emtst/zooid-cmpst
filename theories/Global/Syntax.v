From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.

From Paco Require Import paco paco2.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.Common.

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

Lemma g_ty_ind :
  forall (P : g_ty -> Prop),
    P g_end ->
    (forall v, P (g_var v)) ->
    (forall G, P G -> P (g_rec G)) ->
    (forall p q Ks, (forall K, member K Ks -> P K.2.2) ->
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

Fixpoint depth (a : g_ty) :=
  match a with
  | g_end
  | g_var _ => 0
  | g_rec G => (depth G).+1
  | g_msg _ _ K => (foldr maxn 0 (map (fun x=> depth x.2.2) K)).+1
  end.

Fixpoint participants (G : g_ty) :=
  match G with
  | g_end
  | g_var _ => [::]
  | g_rec G => participants G
  | g_msg p q Ks => p::q::flatten [seq participants K.2.2 | K <- Ks]
  end.

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
            | K1::Ks1, K2::Ks2 => (K1.1 == K2.1)
                                    && (K1.2.1 == K2.2.1)
                                    && eq_g_ty K1.2.2 K2.2.2
                                    && eqL Ks1 Ks2
            | _, _ => false
            end) Ks1 Ks2
  | _, _ => false
  end.

Definition eq_alt (l r : lbl * (mty * g_ty)) :=
  (l.1 == r.1) && (l.2.1 == r.2.1) && eq_g_ty l.2.2 r.2.2.

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
  case: g_ty_eqP=>[<-|H]; first by apply: ReflectT.
  by apply: ReflectF =>[[/H]].
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
    g_msg p q [seq (K.1, (K.2.1, g_open d G2 K.2.2)) | K <- Ks]
  end.
Notation "{ k '~>' v } G":= (g_open k v G) (at level 30, right associativity).
Notation "G '^' v":= (g_open 0 (g_var v) G) (at level 30, right associativity).

Definition unroll G := g_open 0 (g_rec G) G.

Lemma g_open_msg_rw d G2 FROM TO CONT:
  g_open d G2 (g_msg FROM TO CONT)
  = g_msg FROM TO [seq (K.1, (K.2.1, g_open d G2 K.2.2)) | K <- CONT].
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
  move=>h1 h2; apply: notin_part_g_open_strong; by [apply h2 | rewrite h1].
Qed.

Lemma notin_part_g_open r G:
  r \notin participants G -> r \notin participants (g_open 0 (g_rec G) G).
Proof.
  by apply same_notin_part_g_open; rewrite //=.
Qed.

Fixpoint g_fidx (d : nat) (G : g_ty) : seq nat :=
  match G with
  | g_var v => if v >= d then [:: v - d] else [::]
  | g_rec G => g_fidx d.+1 G
  | g_msg p q Ks => flatten [seq g_fidx d K.2.2 | K <- Ks]
  | g_end => [::]
  end.
Definition g_closed (G : g_ty) := g_fidx 0 G == [::].

Lemma gfbvar_next n G :
  g_fidx n G == fset0 ->
  g_fidx n.+1 G = fset0.
Proof.
  elim: G n=>[//|v|G Ih|p q Ks Ih] n/=.
  - case: v=>//= m H; case: ifP=>// n_m; move: H.
    by move: (leq_trans (leqnSn n) n_m)=>->.
  - by apply: Ih.
  - rewrite flatten_eq_nil member_map=>H; apply/eqP.
    by rewrite flatten_eq_nil member_map=> K M; move: (Ih K M n (H K M))=>->.
Qed.

Fixpoint guarded d G :=
  match G with
  | g_end => true
  | g_var v => v >= d
  | g_rec G => guarded d.+1 G
  | g_msg _ _ Ks => all (fun K => guarded 0 K.2.2) Ks
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
  | g_msg _ _ Ks => all (fun K => guarded' K.2.2) Ks
  end.

Lemma guarded_next n G : guarded n.+1 G = ~~ g_binds n G && guarded n G.
Proof. by elim: G n=>//= v n; rewrite ltn_neqAle eq_sym. Qed.

Lemma guarded_binds G : guarded 0 G = guarded' G.
Proof.
  elim: G=>[||G|_ _ Ks Ih]//=; first by move=><-;apply/guarded_next.
  elim: Ks Ih=>[//|K Ks Ih']/= Ih; rewrite Ih; last by left.
  by rewrite Ih' // => K' /or_intror/Ih.
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
  guarded dG' G -> g_fidx n G == [::] -> guarded dG G.
Proof.
  elim: G =>[|m|G Ih|p q Ks Ih]// in n dG dG' *.
  - by move=> /leq_trans-H /= /H->.
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
     case: ifP=>//; rewrite ltn_neqAle =>/(rwP negPf).
     rewrite negb_and negbK eq_sym; by move=>/orP-[->//|/negPf->].
   - by apply: (Ih n.+1); rewrite gfbvar_next.
   - rewrite -map_comp/comp/=; move=>/flatten_eq_nil/member_map-H.
     by apply/flatten_eq_nil/member_map=>K M; apply: Ih=>//; apply: H.
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

Fixpoint is_end g :=
  match g with
  | g_rec g => is_end g
  | g_end => true
  | _ => false
  end.

Lemma recdepth_unroll g :
  is_end g -> rec_depth g = rec_depth (unroll g).
Proof.
  move=>END; have: (is_end (g_rec g)) by [].
  rewrite /unroll; move: (g_rec g)=>g' END'.
  by elim: g 0 END=>// g Ih n /=/(Ih n.+1)->.
Qed.

Lemma isend_unroll g :
  is_end g -> is_end (unroll g).
Proof.
  move=>END; have: (is_end (g_rec g)) by [].
  rewrite /unroll; move: (g_rec g)=>g' END'.
  by elim: g 0 END=>// g Ih n /=/(Ih n.+1)->.
Qed.

Fixpoint non_empty_cont G :=
  match G with
  | g_msg _ _ Ks => ~~ nilp Ks && all id [seq non_empty_cont K.2.2 | K <- Ks]
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


Lemma precond_parts g :
  g_precond g -> ~~ nilp (participants g) \/ is_end g.
Proof.
  move=>/andP-[/andP-[CG GG]  _]; move: CG GG; rewrite /g_closed.
  elim: g 0.
  - by move=> n _ _; right.
  - by move=>v n /= H E; move: E H=>->.
  - by move=> G Ih n /=; apply/Ih.
  - by move=> p q Ks _ n  _ _; left.
Qed.

End Syntax.
