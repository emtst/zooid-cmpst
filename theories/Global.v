From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.Atom.
Require Import MPST.AtomSets.
Require Import MPST.Forall.
Require Import MPST.LNVar.
Require Import MPST.Actions.

Section Syntax.

  (**
   * Global Types
   *)
  Inductive g_ty :=
  | g_end
  | g_var (v : rvar)
  | g_rec (G : g_ty)
  | g_msg (p : role) (q : role) (Ks : seq (lbl * (mty * g_ty))).

  Open Scope mpst_scope.

  Arguments bv [_] _.
  Notation gfv a := (g_var (fv a)).
  Notation gbv n := (g_var (bv n)).

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
    | g_var v => open g_var d G2 v
    | g_rec G => g_rec (g_open d.+1 G2 G)
    | g_msg p q Ks =>
      g_msg p q [seq (K.lbl, (K.mty, g_open d G2 K.cnt)) | K <- Ks]
    end.
  Notation "{ k '~>' v } G":= (g_open k v G) (at level 30, right associativity).
  Notation "G '^' v":= (g_open 0 (gfv v) G) (at level 30, right associativity).

  Fixpoint g_close (v : atom) (d : nat) (G1 : g_ty) :=
    match G1 with
    | g_end => G1
    | g_var gv => g_var (close v d gv)
    | g_rec G => g_rec (g_close v d.+1 G)
    | g_msg p q Ks => g_msg p q [seq (K.lbl, (K.mty, g_close v d K.cnt)) | K <- Ks]
    end.
  Notation "{ k '<~' v } G":= (g_close v k G) (at level 30, right associativity).

  Open Scope fset_scope.
  Fixpoint g_fvar (G : g_ty) : {fset atom} :=
    match G with
    | g_var v => fvar v
    | g_rec G => g_fvar G
    | g_msg p q Ks => fsetUs [seq g_fvar K.cnt | K <- Ks]
    | g_end => fset0
    end.

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

  Fixpoint g_fbvar (d : nat) (G : g_ty) : {fset nat} :=
    match G with
    | g_var v => fbvar d v
    | g_rec G => g_fbvar d.+1 G
    | g_msg p q Ks => fsetUs [seq g_fbvar d K.cnt | K <- Ks]
    | g_end => fset0
    end.

  Definition g_lc (G : g_ty) := g_fbvar 0 G = fset0.

  Definition g_closed (G : g_ty) :=
    (g_fbvar 0 G == fset0) && (g_fvar G == fset0).

  Lemma in_gfvar_gfv (a a' : atom) : (a \in g_fvar (gfv a')) = (a == a').
  Proof.
    rewrite /g_fvar; case: fset1P=>[->|].
    - by rewrite eq_refl.
    - by move=> /eqP/negPf->.
  Qed.

  Lemma gopen_gfv n X (a : atom) : g_open n X (gfv a) = gfv a.
  Proof. by []. Qed.

  Lemma gclose_gfv n X (a : atom) :
    g_close X n (gfv a) = if X == a then (gbv n) else (gfv a).
  Proof. by rewrite /g_close/close (fun_if g_var). Qed.

  Lemma g_open_close X (G : g_ty) n : X \notin g_fvar G -> {n <~ X}{n ~> gfv X}G = G.
  Proof.
    elim/gty_ind1: G n =>//.
    - by move=> v d /= H; rewrite open_fun /= (open_close d H).
    - move=> G Ih d; rewrite /g_fvar -/(g_fvar _)=>/Ih-{Ih}Ih.
      by rewrite -[in RHS](Ih d.+1).
    - move=> p q Ks Ih n /= H; rewrite -map_comp/comp/=; congr g_msg.
      elim: Ks H Ih => {p} {q} [//|/=[l [t G]] Ks Ih].
      rewrite fsetUs_cons negb_or /= =>/andP-[X_G X_KS] IhKs.
      rewrite (IhKs (l, (t, G)) (or_introl (Logic.eq_refl _)) n X_G) Ih //.
      by move=> K KKs r H; apply: IhKs =>//; right.
  Qed.

  Lemma g_close_open n X (G : g_ty) : n \notin g_fbvar 0 G -> {n ~> gfv X}{n <~ X}G = G.
  Proof.
    move: {1 3}n (add0n n)=>n0; elim/gty_ind2: G 0 n =>///=.
    - by move=> v n n1 <- H; rewrite addnC open_fun close_open.
    - move=> G Ih d n Eq n_in; congr g_rec; apply: (Ih d.+1)=>//.
      by rewrite -Eq.
    - move=> p q Ks /Fa_lift-Fa d n Eq; rewrite notin_fold_all !all_map /preim/=.
      move: (Fa d)=>{Fa}/Fa_lift/(_ n)/Fa_lift/(_ Eq)-Fa.
      move=>/forallbP/(Fa_conj Fa){Fa}.
      rewrite /SimplPred/= =>/Fa_app/Fa_map_eq-Ih.
      rewrite -map_comp /comp/=; congr g_msg => {Eq d n0 p q}.
      by elim: Ks Ih=>[//|/=[l [t G]] Ks Ih [-> /Ih->]].
  Qed.
  Close Scope fset_scope.

  Lemma g_depth_open (G : g_ty) X : depth_gty G = depth_gty (G^X).
  Proof.
    move: 0; elim/gty_ind2: G=>/=//.
    + by move=>v n; rewrite open_fun.
    + by move=> G Ih n; rewrite (Ih n.+1).
    + move=> _ _ Gs /Fa_lift-Ih n; move: (Ih n) => {Ih}/Fa_map_eq.
      rewrite -map_comp /comp/=.
      by elim: Gs=>[//|/=[l G] Gs Ih []<- /Ih-{Ih}[<-]].
  Qed.

  Lemma gfbvar_next n G :
    g_fbvar n G == fset0 ->
    g_fbvar n.+1 G = fset0.
  Proof.
    elim/gty_ind1: G n=>[//|v|G Ih|p q Ks Ih] n/=.
    - case: v=>//= m H; case: ifP=>// n_m; move: H.
      by move: (leq_trans (leqnSn n) n_m)=>->; rewrite -cardfs_eq0 cardfs1.
    - by apply: Ih.
    - rewrite fsetUs_fset0 member_map=>H; apply/eqP.
      by rewrite fsetUs_fset0 member_map=> K M; move: (Ih K M n (H K M))=>->.
  Qed.

  Lemma gopen_closed G :
    g_closed (g_rec G) ->
    g_closed (g_open 0 (g_rec G) G).
  Proof.
    rewrite/g_closed/==>/andP-[G_fbv /eqP-G_fv]; apply/andP; split=>[{G_fv}|{G_fbv}].
    + have: g_fbvar 0 (g_rec G) == fset0 by [].
      move: (g_rec G) => G' G'0.
      elim/gty_ind1: G 0 G'0 G_fbv=>[//|v|G Ih|p q Ks Ih] n G'0/=.
      - case: v=>[//|/= m]; case: ifP; first by rewrite -cardfs_eq0 cardfs1//.
        case: ifP=>[/eqP<-//|/=]; case: ifP=>//.
        by rewrite ltn_neqAle (rwP negPf)=>->->.
      - by apply: (Ih n.+1); rewrite gfbvar_next.
      - rewrite -map_comp/comp/=; move=>/fsetUs_fset0/member_map-H.
        by apply/fsetUs_fset0/member_map=>K M; apply: Ih=>//; apply: H.
    + move: G_fv=>/eqP-G_fv; have: g_fvar (g_rec G) == fset0 by [].
      move: (g_rec G) => G' G'_fv.
      elim/gty_ind1: G 0 G_fv =>[//|v |G Ih | p q Ks Ih] n /=.
      - by case v=>//; case =>[|m]//=; case: ifP.
      - by apply: Ih.
      - rewrite -map_comp/comp !fsetUs_fset0 !member_map=> H K M.
        by apply: Ih => //; apply: H.
  Qed.

  (* Induction scheme that takes into account that g_rec must be opened *)
  Lemma gty_ind3 :
    forall (P : g_ty -> Type),
      P g_end ->
      (forall v, P (g_var v)) ->
      (forall G, (forall X (s : {fset atom}), X \notin s -> P (G ^ X)) ->
                 P (g_rec G)) ->
      (forall p q Ks, (forall K, K \in Ks -> P K.cnt) -> P (g_msg p q Ks)) ->
      forall g : g_ty, P g.
  Proof.
    move=> P P_end P_var P_rec P_msg G.
    move: {-1}(depth_gty G) (leqnn (depth_gty G))=> n; move: n G; elim.
    + by case.
    + move=>n Ih; case=>///=.
      - by move=> G dG; apply: P_rec => X S _; apply: Ih; rewrite -g_depth_open.
      - move=>p q Ks dKs; apply: P_msg=>K /(map_f (fun X => depth_gty X.cnt))/=.
        move=>/in_maximum_leq-dG; move: (leq_trans dG dKs)=>{dG} {dKs}.
        by apply: Ih.
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
