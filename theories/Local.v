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

  Inductive l_ty :=
  | l_end
  | l_var (v : nat)
  | l_rec (L : l_ty)
  | l_msg (a : l_act) (r : role) (Ks : seq (lbl * (mty * l_ty)))
  .

  Open Scope mpst_scope.

  Fixpoint partsL (G : l_ty) :=
    match G with
    | l_end
    | l_var _ => [::]
    | l_rec G => partsL G
    | l_msg a p Ks => p::flatten [seq partsL K.cnt | K <- Ks]
    end.

  Lemma lty_ind :
    forall (P : l_ty -> Prop),
      P l_end ->
      (forall v, P (l_var v)) ->
      (forall G, P G -> P (l_rec G)) ->
      (forall a p Ks, Forall (fun K => P K.cnt) Ks -> P (l_msg a p Ks)) ->
      forall l : l_ty, P l.
  Proof.
    move => P P_end P_var P_rec P_msg.
    fix Ih 1; case=>[|v|L|a r K].
    + by apply: P_end.
    + by apply: P_var.
    + by apply: P_rec.
    + by apply: P_msg; elim: K.
  Qed.

  Fixpoint depth_lty L :=
    match L with
    | l_end
    | l_var _ => 0
    | l_rec L => (depth_lty L).+1
    | l_msg _ _ Ks => (maximum [seq depth_lty K.cnt | K <- Ks]).+1
    end.

  Fixpoint eq_lty x y :=
    match x, y with
    | l_end, l_end => true
    | l_var x, l_var y => x == y
    | l_rec x, l_rec y => eq_lty x y
    | l_msg a1 r1 Ks1, l_msg a2 r2 Ks2
      => (a1 == a2) && (r1 == r2)
           && (fix eqK Ks1 Ks2 :=
                 match Ks1, Ks2 with
                 | [::], [::] => true
                 | K1::Ks1, K2::Ks2 =>
                   (K1.lbl == K2.lbl)
                     && (K1.mty == K2.mty)
                     && eq_lty K1.cnt K2.cnt
                     && eqK Ks1 Ks2
                 | _, _ => false
                 end) Ks1 Ks2
           (* all2 (fun l r => (l.1 == r.1) && eq_lty l.2 r.2) K1 K2 *)
    | _, _ => false
    end.

  Definition eq_lalt (l r : lbl * (mty * l_ty)) :=
    (l.lbl == r.lbl) && (l.mty == r.mty) && eq_lty l.cnt r.cnt.

  Lemma eqmsg_all a1 a2 r1 r2 K1 K2 :
    eq_lty (l_msg a1 r1 K1) (l_msg a2 r2 K2) =
    (a1 == a2) && (r1 == r2) && all2 eq_lalt K1 K2.
  Proof.
    rewrite /=; do 2 (case: eqP=>///= _); move: K1 K2 {r1 r2 a1 a2}.
    by elim=>//[[l1 L1] K1] Ih; case=>//[[l2 L2] K2]/=; rewrite Ih.
  Qed.

  Lemma lty_eqP : Equality.axiom eq_lty.
  Proof.
    rewrite /Equality.axiom; fix Ih 1 => x y.
    case: x => [|v|L|a r K]; case: y =>[|v'|L'|a' r' K']; try (by constructor).
    + by rewrite /eq_lty; case: eqP=>[->|F]; constructor=>//[[/F]].
    + by rewrite /=; case: Ih=>[->|F]; constructor=>//[[/F]].
    + rewrite eqmsg_all; do 2 (case: eqP=>[<-|F]/=;[|constructor=>[[/F]]//]).
      elim: K K'=>[|[l [t L]] K IhK];
        case=>[|[l' [t' L']]K']/=; try (by constructor).
      rewrite {1}/eq_lalt/=; do 2 (case: eqP=>[<-|F];[|constructor=>[[/F]]//]).
      case: Ih=>[<-|F];[|constructor=>[[/F]]//].
      by case: IhK=>[[]<-|F]; constructor=>//[[]]H; apply: F; rewrite H.
  Qed.

  Definition lty_eqMixin := EqMixin lty_eqP.
  Canonical lty_eqType := Eval hnf in EqType l_ty lty_eqMixin.

  Fixpoint l_open (d : nat) (L2 : l_ty) (L1 : l_ty) :=
    match L1 with
    | l_end => L1
    | l_var v => if v == d then L2 else L1
    | l_rec L => l_rec (l_open d.+1 L2 L)
    | l_msg a p Ks =>
      l_msg a p [seq (K.lbl, (K.mty, l_open d L2 K.cnt)) | K <- Ks]
    end.
  Notation "{ k '~>' v } L":= (l_open k v L) (at level 30, right associativity).
  Notation "L '^' v":= (l_open 0 (l_var v) L) (at level 30, right associativity).

  Lemma open_notvar n L L' :
    (forall v : nat, L != l_var v) ->
    (forall v : nat, l_open n L' L != l_var v).
  Proof. by case: L=>//v /(_ v)/eqP. Qed.

  Lemma l_open_msg_rw d L2 a r Ks:
   l_open d L2 (l_msg a r Ks)
   = l_msg a r [seq (K.lbl, (K.mty, l_open d L2 K.cnt)) | K <- Ks].
  Proof. by []. Qed.

  Lemma unzip2_lift A B C (f : B -> C) (K : seq (A * B)) :
    [seq f x | x <- unzip2 K] = unzip2 [seq (x.1, f x.2) | x <- K].
  Proof. by rewrite /unzip2 -!map_comp /comp. Qed.

  Lemma unzip1_map2 A B C (f : B -> C) (K : seq (A * B)) :
    unzip1 K = unzip1 [seq (x.1, f x.2) | x <- K].
  Proof. by rewrite /unzip1 -map_comp /comp. Qed.

  Lemma map2_zip A B C (f : B -> C) (K : seq (A * B)) :
    zip (unzip1 K) [seq f x | x <- unzip2 K] = [seq (x.1, f x.2) | x <- K].
  Proof. by rewrite unzip2_lift (unzip1_map2 f) zip_unzip. Qed.

  Fixpoint l_fidx (d : nat) (L : l_ty) : {fset nat} :=
    match L with
    | l_end => fset0
    | l_var v => if v >= d then [fset v - d]%fset else fset0
    | l_rec L => l_fidx d.+1 L
    | l_msg _ _ K => fsetUs [seq l_fidx d lL.cnt | lL <- K]
    end.

  Lemma lty_ind2 :
    forall (P : l_ty -> Prop),
      P l_end ->
      (forall v, P (l_var v)) ->
      (forall L, P L -> P (l_rec L)) ->
      (forall a p Ks, (forall K, K \in Ks -> P K.cnt) -> P (l_msg a p Ks)) ->
      forall l : l_ty, P l.
  Proof.
    move => P P_end P_var P_rec P_msg L.
    move: {-1}(depth_lty L) (leqnn (depth_lty L))=> n; move: n L; elim.
    + by case.
    + move=>n Ih; case=>/=//.
      - by move=>L D; apply:P_rec; apply: Ih.
      - move=> a r Ks D;apply: P_msg=>K /(map_f (fun X => depth_lty X.cnt)).
        move=>/in_maximum_leq-/=dG; move: (leq_trans dG D)=>{dG} {D}.
        by apply: Ih.
  Qed.

  Definition l_closed (L : l_ty) := l_fidx 0 L == fset0.

  Lemma lfbvar_next n G :
    l_fidx n G == fset0 ->
    l_fidx n.+1 G = fset0.
  Proof.
    elim/lty_ind2: G n=>[//|v|G Ih|p q Ks Ih] n/=.
    - case: v=>//= m H; case: ifP=>// n_m; move: H.
      by move: (leq_trans (leqnSn n) n_m)=>->; rewrite -cardfs_eq0 cardfs1.
    - by apply: Ih.
    - rewrite fsetUs_fset0 member_map=>H; apply/eqP.
      rewrite fsetUs_fset0 member_map=> K /memberP-M.
      by move: M (Ih K M n)=>/memberP-M /(_ (H K M))=>->.
  Qed.

  Lemma lopen_closed G :
    l_closed (l_rec G) ->
    l_closed (l_open 0 (l_rec G) G).
  Proof.
    rewrite/l_closed/==>G_fbv.
    have: l_fidx 0 (l_rec G) == fset0 by [].
    move: (l_rec G) => G' G'0.
    elim/lty_ind2: G 0 G'0 G_fbv=>[//|v|G Ih|p q Ks Ih] n G'0/=.
    - move=> H; case: ifP=>[//|/=]; case: ifP=>//; move: H.
      case: ifP=>//; first by rewrite -cardfs_eq0 cardfs1//.
      rewrite ltn_neqAle =>/(rwP negPf); rewrite negb_and negbK eq_sym.
      by move=>/orP-[->//|/negPf->].
    - by apply: (Ih n.+1); rewrite lfbvar_next.
    - rewrite -map_comp/comp/=; move=>/fsetUs_fset0/member_map-H.
      apply/fsetUs_fset0/member_map=>K /memberP-M.
      by apply: Ih=>//; apply: H; apply/memberP.
  Qed.

  Fixpoint lguarded d L :=
    match L with
    | l_end => true
    | l_var v => v >= d
    | l_rec L => lguarded d.+1 L
    | l_msg _ _ Ks => all (fun K => lguarded 0 K.cnt) Ks
    end.

  Fixpoint l_binds n L :=
    match L with
    | l_var v => v == n
    | l_rec L => l_binds n.+1 L
    | _ => false
    end.

  Fixpoint lguarded' L :=
    match L with
    | l_end
    | l_var _ => true
    | l_rec L => ~~ l_binds 0 L && lguarded' L
    | l_msg _ _ Ks => all (fun K => lguarded' K.cnt) Ks
    end.

  Lemma lguarded_next n G : lguarded n.+1 G = ~~ l_binds n G && lguarded n G.
  Proof. by elim/lty_ind2: G n=>//= v n; rewrite ltn_neqAle eq_sym. Qed.

  Lemma lguarded_binds G : lguarded 0 G = lguarded' G.
  Proof.
    elim/lty_ind2: G=>[||G|_ _ Ks Ih]//=; first by move=><-;apply/lguarded_next.
    elim: Ks Ih=>[//|K Ks Ih']/= Ih; rewrite Ih ?in_cons ?eq_refl //.
    by rewrite Ih' // => K' H; apply/Ih; rewrite in_cons orbC H.
  Qed.

  Lemma lguarded_rec d L
    : lguarded d (l_rec L) -> forall s, s <= d -> ~~ l_binds s L.
  elim/lty_ind2: L=>[|v|L /= Ih|a p Ks Ih]// in d *.
  - move=>/= vd s sd; move: (leq_ltn_trans sd vd).
    by rewrite eq_sym ltn_neqAle=>/andP-[].
  - by rewrite /==>/Ih-{Ih}Ih s Lsd; apply/Ih.
  Qed.


  (* Inductive LGuarded : nat -> l_ty -> Prop := *)
  (* | L_end d : *)
  (*     LGuarded d l_end *)
  (* | L_var d v : *)
  (*     LGuarded d (l_var v) *)
  (* | L_rec_var d v : *)
  (*     v > d -> *)
  (*     LGuarded d (l_rec (l_var v)) *)
  (* | L_rec d L : *)
  (*     (forall v, L != l_var v) -> *)
  (*     LGuarded d.+1 L -> *)
  (*     LGuarded d (l_rec L) *)
  (* | L_msg d a p Ks : *)
  (*     LAllGuarded Ks -> *)
  (*     LGuarded d (l_msg a p Ks) *)
  (* with LAllGuarded : seq (lbl * (mty * l_ty)) -> Prop := *)
  (* | L_nil : *)
  (*     LAllGuarded [::] *)
  (* | L_cons K Ks : *)
  (*     LGuarded 0 K.cnt -> *)
  (*     LAllGuarded Ks -> *)
  (*     LAllGuarded (K :: Ks) *)
  (* . *)

  (* Lemma lrec_not_guarded d G' : *)
  (*   ~ LGuarded d.+1 G' -> *)
  (*   (forall v : nat, G' != l_var v) -> *)
  (*   ~ LGuarded d (l_rec G'). *)
  (* Proof. *)
  (*   move=> N_GG' Ne; move: {-1}d (eq_refl d) {-1}(l_rec G') (eq_refl (l_rec G')). *)
  (*   move=> d' d_d' G Eq_G H; case: H d_d' Eq_G=>//. *)
  (*   + by move=> d0 v _ _; move: Ne; rewrite !eqE/==>/(_ v)-N E;move:E N=>->. *)
  (*   + move=> d0 G0 _ GG' /eqP-E1; rewrite !eqE/==>/eqP-E2. *)
  (*     by move: E1 E2 GG'=><-<-/N_GG'. *)
  (* Qed. *)

  (* Lemma lalt_eq a1 p1 Ks1 a2 p2 Ks2 : *)
  (*   ((l_msg a1 p1 Ks1) == (l_msg a2 p2 Ks2)) = *)
  (*   (a1 == a2) && (p1 == p2) && (Ks1 == Ks2). *)
  (* Proof. *)
  (*   rewrite eqE/=; do 2 case: eqP=>//=; move=> _ _ {p1 a1 p2 a2}. *)
  (*   elim: Ks1=>[|K1 Ks1 Ih] in Ks2 *; case: Ks2=>[|K2 Ks2]//=. *)
  (*   by rewrite Ih; do ! rewrite !eqE/=; rewrite -!eqE !andbA. *)
  (* Qed. *)

  (* Lemma guardedP d G : reflect (LGuarded d G) (lguarded d G). *)
  (* Proof. *)
  (*   move: G d; fix Ih 1; case=> [|v|G|p q Ks] d/=; try do ! constructor. *)
  (*   - move: {-1} G (eq_refl G) => G' Eq. *)
  (*     case: G' Eq=>[|n|G'|p q Ks]; try do ! constructor. *)
  (*     * case: (boolP (d < n))=>[d_lt_n|d_ge_n]; do ! constructor =>//. *)
  (*       move: {-1}d (eq_refl d) {-1}(l_rec (l_var n)) (eq_refl (l_rec (l_var n))). *)
  (*       move=> d' d_d' G' Eq_G H; case: H d_d' Eq_G=>//. *)
  (*       + move=> d0 v d_lt_n /eqP-H; move: H d_lt_n=><-{d0} d_lt_n H. *)
  (*         by move: H d_lt_n d_ge_n; do 2 rewrite !eqE/=; move=>/eqP<-->. *)
  (*       + move=> {d'} d' G'' Neq _ _; rewrite !eqE/=. *)
  (*         by case: G'' Neq=>// v /(_ v)/eqP. *)
  (*     * move=> GG'; have: (forall v, G != l_var v) by move: GG'=>/eqP->. *)
  (*       move: GG'=>/eqP<-; case: (Ih G d.+1)=>[GG'|N_GG']; do ! constructor=>//. *)
  (*       by apply/lrec_not_guarded. *)
  (*     * move=> GG'; have: (forall v, G != l_var v) by move: GG'=>/eqP->. *)
  (*       move: GG'=>/eqP<-; case: (Ih G d.+1)=>[GG'|N_GG']; do ! constructor=>//. *)
  (*       by apply/lrec_not_guarded. *)
  (*   - elim: Ks=>[|K Ks]/=; try do ! constructor=>//. *)
  (*     case: (Ih K.cnt 0)=>[GK [GG|N_GG]|N_GK]/=; try do ! constructor=>//. *)
  (*     * case Eq: (l_msg p q Ks) / GG=>// [d' p' q' Ks' GKs]. *)
  (*       move: Eq=>/eqP; rewrite lalt_eq =>/andP-[_ Eq]. *)
  (*       by move: Eq GKs=>/eqP<-. *)
  (*     * move=> NGG; case Eq: (l_msg _ _ _) / NGG=>// [d' p' q' Ks' GKs]. *)
  (*       move: Eq=>/eqP; rewrite lalt_eq =>/andP-[_ Eq]. *)
  (*       move: Eq GKs=>/eqP<- H; case Eq: (K::Ks) / H =>// [K' Ks'' _ GKs]. *)
  (*       by move: Eq GKs=>[_ <-] /(L_msg d p q)/N_GG. *)
  (*     * move=> NGG; case Eq: (l_msg _ _ _) / NGG=>// [d' p' q' Ks' GKs]. *)
  (*       move: Eq=>/eqP; rewrite lalt_eq =>/andP-[_ Eq]. *)
  (*       move: Eq GKs=>/eqP<-H'; case Eq: (K::Ks) / H' =>// [K' Ks'' GK0 _]. *)
  (*       by move: Eq GK0=>[<- _] /N_GK. *)
  (* Qed. *)

  Fixpoint lrec_depth L :=
    match L with
    | l_rec G => (lrec_depth G).+1
    | _ => 0
    end.

  Fixpoint lunroll d G :=
    match d with
    | 0 => G
    | d.+1 =>
      match G with
      | l_rec G' => lunroll d (l_open 0 G G')
      | _ => G
      end
    end.

  Lemma lguarded_match d G :
    match G with
    | l_var v => d < v
    | _ => lguarded d.+1 G
    end ->
    (exists v, (G == l_var v) && (d < v)) \/
    (forall v, (G != l_var v)) /\ lguarded d.+1 G.
  Proof.
    case: G=>[|||]//=; try by right.
    by move=> n Eq; left; exists n; rewrite eq_refl.
  Qed.

  Lemma lguarded_recdepth d G m :
    lguarded d G ->
    m < d ->
    forall G', lrec_depth G = lrec_depth ({m ~> G'} G).
  Proof.
    elim/lty_ind2: G=>[|n|G Ih|p q Ks Ih]//= in d m *.
    - move=>dn md G; case: ifP=>[/eqP-E|ne//].
      by move: E dn md=>-> /leq_ltn_trans-H /H; rewrite ltnn.
    - by move=> GG md G'; rewrite (Ih _ m.+1 GG _ G').
  Qed.

  Lemma lty_not_var A G (b1 : nat -> A) (b2 : A) :
    (forall v : nat, G != l_var v) ->
    match G with | l_var v => b1 v | _ => b2 end = b2.
  Proof. by case: G =>[|n /(_ n)/eqP||]. Qed.

  Lemma lguarded_depth_gt dG dG' G :
    lguarded dG' G -> l_closed G -> lguarded dG G.
  Proof.
    rewrite /l_closed=> H H'; move: 0 (leq0n dG') H H'.
    elim/lty_ind2: G =>[|n|G Ih|p q Ks Ih]// in dG dG' *.
    - by move=> m /leq_trans-H /= /H->; rewrite -cardfs_eq0 cardfs1.
    - by move=> n ndG' /=; apply/Ih.
  Qed.

  Lemma lclosed_not_var G :
    l_closed G ->
    forall v, G != l_var v.
  Proof.
    rewrite /l_closed.
    by case: G=>//= v; rewrite -cardfs_eq0 cardfs1.
  Qed.

  Lemma lopen_not_var d G G' :
    l_closed G ->
    (forall v, G' != l_var v) ->
    forall v, {d ~> G} G' != l_var v.
  Proof. by case: G'=>// n _ /(_ n)/eqP. Qed.

  Lemma lguarded_open d1 d2 G G' :
    lguarded 0 G' ->
    l_closed G' ->
    lguarded d1 G ->
    lguarded d1 ({d2 ~> G'} G).
  Proof.
    elim/lty_ind2: G=>[|n|G Ih|p q Ks Ih]//= in d1 d2 *.
    - by case: ifP=>// _ /lguarded_depth_gt-H /H-{H}H.
    - by apply/Ih.
    - move=> GG' CG'; elim: Ks=>[|K Ks IhK]//= in Ih *.
      move: (Ih K); rewrite in_cons eq_refl=>/(_ is_true_true _ _ GG' CG')-H.
      move=>/andP-[GK GKs]; move: H=>/(_ _ _ GK)->//=.
      by apply/IhK=>// K0 MK0; apply/Ih; rewrite in_cons orbC MK0.
  Qed.

  Lemma lguarded_gt d d' G :
    d >= d' ->
    lguarded d G ->
    lguarded d' G.
  Proof.
    elim/lty_ind2: G=>[|n|G Ih|p q Ks Ih]//= in d d' *.
    - by move=>/leq_trans-H /H.
    - by move=> H; apply/Ih.
  Qed.

  Lemma lunroll_guarded G :
    l_closed G ->
    lguarded 0 G ->
    forall G', lunroll (lrec_depth G) G != l_rec G'.
  Proof.
    move: {-2}(lrec_depth G) (eq_refl (lrec_depth G)) => n.
    elim: n => [|n Ih]/= in G *; case: G=>// G n_rd CG GG; move: n_rd.
    rewrite eqE/=-eqE => n_rd.
    have/=GG': (lguarded 0 (l_rec G)) by [].
    move: n_rd; rewrite (lguarded_recdepth GG' (ltn0Sn 0) (l_rec G))=>n_rd.
    apply/Ih=>//; first by apply/lopen_closed.
    by apply/lguarded_open=>//; apply/lguarded_gt; last by apply/GG'.
  Qed.

  Fixpoint l_isend L {struct L}:=
    match L with
    | l_rec L => l_isend L
    | l_end => true
    | _ => false
    end.

  Lemma isend_open n L' L :
    l_isend L -> l_open n L' L = L.
  Proof.
    elim/lty_ind2: L=>[|v|L Ih|a p KS Ih]//= in n *; move=> END.
    by rewrite Ih.
  Qed.

  Lemma keep_unrolling L :
    l_isend L -> exists m, l_end = lunroll m L.
  Proof.
    elim/lty_ind2: L=>[||L Ih|]//; [move=>_| move=>/=END; move:(Ih END)=>[n U]].
    - by exists 0.
    - by exists n.+1=>/=; rewrite (isend_open 0 _ END).
  Qed.


 Lemma l_closed_no_binds_aux m n L: m <= n -> l_fidx m L == fset0
    -> l_binds n L = false.
  Proof.
  elim: L m n; rewrite //=.
  + move=> v m n le; case: ifP;
      [by rewrite -cardfs_eq0 cardfs1 //=
      | by move=> lefalse; elim; apply: ltn_eqF;
      apply: (leq_trans _ le); move: (negbT lefalse); rewrite-ltnNge //=].
  + by move=> L IH m n le; apply: IH; rewrite //=.
  Qed.

  Lemma l_closed_no_binds n L: l_closed L -> l_binds n L = false.
  Proof. by apply: l_closed_no_binds_aux. Qed.

  Lemma l_binds_open m n L L1: n != m -> l_closed L1
    -> l_binds m (l_open n L1 L) = l_binds m L.
  Proof.
  elim: L m n L1.
  + by move=> m n L1 neq closed; rewrite /l_binds //=.
  + move=> v m n L1 neq closed.
    rewrite /l_binds //=; case: ifP => //=; rewrite <-(rwP eqP); move=>->.
    move: (@l_closed_no_binds m _ closed); rewrite /l_binds; move =>->.
    by move: (negbTE neq).
  + by move=> L IH m n L1 neq closed; rewrite //=; apply: IH.
  + by [].
  Qed.

End Syntax.

Section Semantics.

  Open Scope mpst_scope.

  CoInductive rl_ty :=
  | rl_end
  | rl_msg (a : l_act) (R : role) (C : lbl /-> mty * rl_ty)
  .

  Definition lty_rel := rel2 l_ty (fun=>rl_ty).
  Inductive l_unroll (r : lty_rel) : l_ty -> rl_ty -> Prop :=
  | lu_end :
      @l_unroll r l_end rl_end
  | lu_rec G G' :
      r (l_open 0 (l_rec G) G) G' ->
      @l_unroll r (l_rec G) G'
  | lu_msg a p Ks C :
      l_unroll_all r Ks C ->
      @l_unroll r (l_msg a p Ks) (rl_msg a p C)
  with l_unroll_all (r : lty_rel)
       : seq (lbl * (mty * l_ty)) ->
         (lbl /-> mty * rl_ty) ->
         Prop :=
  | lu_nil : l_unroll_all r [::] (empty _)
  | lu_cons l t G G' Ks C' :
      r G G' ->
      l_unroll_all r Ks C' ->
      l_unroll_all r ((l, (t, G)) :: Ks) (extend l (t, G') C')
  .
  Hint Constructors l_unroll.
  Hint Constructors l_unroll_all.

  Scheme lunroll_ind := Induction for l_unroll Sort Prop
  with lunrollall_ind := Induction for l_unroll_all Sort Prop.

  Lemma l_unroll_monotone : monotone2 l_unroll.
  Proof.
    move=>IL CL r r' U H; move: IL CL U.
    elim/lty_ind2=>[|V|L IH|a F Ks IH] CL//=;
      case E:_ _/ =>[|G G' R|a' F' Ks' C U]//.
    - by move: E R => [<-] /H; constructor.
    - constructor; move: E U=>[_ _<-] {a' F' Ks'}.
      by elim=>[|l t G G' Ks0 C' /H-R U Ih1]; constructor.
  Qed.
  Hint Resolve l_unroll_monotone.

  Definition LUnroll IL CL := paco2 l_unroll bot2 IL CL.

  Definition lu_unfold := paco2_unfold l_unroll_monotone.

  Lemma LUnroll_ind n iG cG :
    LUnroll iG cG <-> LUnroll (lunroll n iG) cG.
  Proof.
    split.
    - elim: n =>[//|n Ih] in iG cG *; case: iG=>//= iL /lu_unfold.
      by case E: _ _/ => [|L L' [|]|]//; move: E=>[->]; apply/Ih.
    - elim: n =>// n Ih in iG cG *; case: iG=>//= G /Ih-H1.
      by apply/paco2_fold; constructor; left.
  Qed.

  Lemma lunroll_end cL :
    LUnroll l_end cL -> cL = rl_end.
  Proof. by move=> /lu_unfold-LU; case Eq: _ _ / LU. Qed.

  Lemma l_guarded_unroll iG :
    l_closed (l_rec iG) -> lguarded 0 (l_rec iG) ->
    lguarded 0 (l_open 0 (l_rec iG) iG).
  Proof.
    move=> C GG; have GG': (lguarded 1 iG) by move:GG C=>/=; case: iG.
    by move: (lguarded_open 0 GG C GG')=>/lguarded_depth_gt/(_ (lopen_closed C)).
  Qed.

  Lemma l_guarded_nunroll n iL :
    l_closed iL -> lguarded 0 iL -> lguarded 0 (lunroll n iL).
  Proof.
    elim: n iL=>[|n Ih]//;case=>// iG CG /(l_guarded_unroll CG)/Ih-H/=.
    by apply/H/lopen_closed.
  Qed.

  Lemma l_closed_unroll n iL :
    l_closed iL -> l_closed (lunroll n iL).
  Proof. by elim: n iL=>[|n Ih]//=; case=>//= iG /lopen_closed/Ih. Qed.

  Lemma v_lty G : (exists v, G = l_var v) \/ (forall v, G != l_var v).
  Proof. by case: G; try (by right); move=>v;left;exists v. Qed.

  Lemma lguarded_lbinds_lt s Lr :
    l_binds s Lr = false ->
    lguarded s Lr ->
    lguarded s.+1 Lr.
  Proof.
    move: {-1}(lrec_depth Lr) (erefl (lrec_depth Lr))=> n E.
    elim: n=>[|n Ih] in s Lr E *.
    - by case: Lr E=>//= v _ /(rwP negPf); rewrite ltn_neqAle eq_sym=>->->.
    - case: Lr E=>//= L [/Ih-E]; apply/E.
  Qed.


  Notation renv := {fmap role -> rl_ty}.
  Notation qenv := {fmap role * role -> seq (lbl * mty) }.

  Definition enq (qs : {fmap (role * role) -> (seq (lbl * mty))}) k v :=
    match qs.[? k] with
    | Some vs => qs.[ k <- app vs [:: v] ]
    | None => qs.[ k <- [:: v]]
    end%fmap.

  Definition deq (qs : {fmap (role * role) -> (seq (lbl * mty))}) k :=
    match qs.[? k] with
    | Some vs =>
      match vs with
      | v :: vs => if vs == [::] then Some (v, qs.[~ k])
                   else Some (v, qs.[k <- vs])
      | [::] => None
      end
    | None => None
    end%fmap.

  Definition do_act (P : renv) a p q l t :=
    match P.[? p]  with
    | Some Lp =>
      match Lp with
      | rl_msg a' q' Ks =>
        match Ks l with
        | Some (t', Lp) =>
          if (a == a') && (q == q') && (t == t')
          then Some P.[p <- Lp]
               (*if Lp is rl_end
               then Some P.[~ p]
               else Some P.[p <- Lp]*)
          else None
        | None => None
        end
      | _ => None
      end
    | None => None
    end%fmap.

  Lemma doact_send (E : renv) p q lb t KsL Lp :
    (E.[? p]%fmap = Some (rl_msg l_send q KsL)) ->
    (KsL lb = Some (t, Lp)) ->
    exists E', (do_act E l_send p q lb t = Some E').
  Proof.
    move=>H1 H2; rewrite /do_act H1 H2 !eq_refl/=.
    by exists E.[ p <- Lp]%fmap.
    (*case: Lp H2 =>[|a r Ks]; [|set (Lp := rl_msg _ _ _)].
    - by (exists E.[~ p]%fmap).
    - by exists E.[ p <- Lp]%fmap.*)
  Qed.



  Definition rlty_rel := rl_ty -> rl_ty -> Prop.
  Inductive EqL_ (r : rlty_rel) : rlty_rel :=
  | el_end : @EqL_ r rl_end rl_end
  | el_msg a p C1 C2 :
      same_dom C1 C2 ->
      R_all r C1 C2 ->
      @EqL_ r (rl_msg a p C1) (rl_msg a p C2).
  Hint Constructors EqL_.
  Definition EqL L1 L2 := paco2 EqL_ bot2 L1 L2.

  Lemma EqL_monotone : monotone2 EqL_.
  Proof.
    move=>L1 L2 r r' E H; elim: E =>[|a p C1 C2 D E]//; constructor=>//.
    by move: E; rewrite /R_all=>E L Ty G G' /E-{E}E /E/H.
  Qed.
  (*Hint Resolve EqL_monotone. *)

  Lemma EqL_refl CL : EqL CL CL.
  Proof.
    move: CL {-1 3}CL (erefl CL).
    apply/paco2_acc=> r0 _ CIH CL CL'<- {CL'}.
    apply/paco2_fold.
    case: CL=>//a R C; constructor.
    - by move=> Lb Ty; split=>[[CL ->]|[CL ->]]; exists CL.
    - by move=> Lb Ty CG CG'-> [->]; right; apply: CIH.
  Qed.
  (*Hint Resolve EqL_refl. *)



  Open Scope fmap_scope.
  (** lstep a Q P Q' P' is the 'step' relation <P, Q> ->^a <P', Q'> in Coq*)
  Inductive lstep : act -> renv * qenv -> renv * qenv -> Prop :=
  | ls_send t p q lb (P P' : renv) (Q Q' : qenv) :
      Q' == enq Q (p, q) (lb, t) ->
      do_act P l_send p q lb t = Some P' ->
      lstep (a_send p q lb t) (P, Q) (P', Q')
  | ls_recv t p q lb (P P' : renv) (Q Q' : qenv) :
      deq Q (p, q) == Some ((lb, t), Q') ->
      do_act P l_recv q p lb t = Some P' ->
      lstep (a_recv p q lb t) (P, Q) (P', Q')
  .

  Definition rel_trc := trace -> renv*qenv -> Prop.
  Inductive l_lts_ (r : rel_trc) : rel_trc :=
  | lt_end : @l_lts_ r tr_end ([fmap], [fmap])
  | lt_next a t P P' :
      lstep a P P' ->
      r t P' ->
      @l_lts_ r (tr_next a t) P.
  Hint Constructors l_lts_.
  Lemma l_lts_monotone : monotone2 l_lts_.
  Proof. pmonauto. Qed.

  Definition l_lts t L := paco2 l_lts_ bot2 t L.
  Derive Inversion llts_inv with (forall tr G, l_lts tr G) Sort Prop.

End Semantics.

Hint Constructors EqL_.
Hint Resolve EqL_monotone.
Hint Resolve EqL_refl.
