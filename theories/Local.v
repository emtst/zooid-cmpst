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

  Definition do_act_l_ty (L: l_ty) (A : act) : option l_ty :=
    let: (mk_act a p q l t) := A in
    match lunroll (lrec_depth L) L with
    | l_msg a' q' Ks =>
      match find_cont Ks l with
      | Some (t', Lp) =>
        if (a == a') && (q == q') && (t == t')
        then Some Lp
        else None
      | None => None
      end
    | _ => None
    end.

  Definition run_act_l_ty (L: l_ty) (A : act) : l_ty := odflt L (do_act_l_ty L A).

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
      same_dom (find_cont Ks) C ->
      R_all r (find_cont Ks) C ->
      @l_unroll r (l_msg a p Ks) (rl_msg a p C)
  .
  Hint Constructors l_unroll.

  Scheme lunroll_ind := Induction for l_unroll Sort Prop.

  Lemma l_unroll_monotone : monotone2 l_unroll.
  Proof.
    move=>IL CL r r' U H; move: IL CL U.
    elim/lty_ind2=>[|V|L IH|a F Ks IH] CL//=;
      case E:_ _/ =>[|G G' R|a' F' Ks' C D U]//.
    - by move: E R => [<-] /H; constructor.
    - by constructor=>// l Ty IL {}CL H0 /(U _ _ _ _ H0)/H.
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

  CoFixpoint l_expand (l : l_ty) : rl_ty :=
    match lunroll (lrec_depth l) l with
    | l_msg a T Ks =>
      rl_msg a T
             (fun l =>
                match find_cont Ks l with
                | Some (Ty, L) => Some (Ty, l_expand L)
                | None => None
                end)
    | _ => rl_end
    end.

  Lemma rltyU G : G = match G with
                      | rl_msg a T C => rl_msg a T C
                      | rl_end => rl_end
                      end.
  Proof. by case: G. Qed.

  Fixpoint l_non_empty_cont G :=
    match G with
    | l_msg _ _ Ks => ~~ nilp Ks && all id [seq l_non_empty_cont K.cnt | K <- Ks]
    | l_rec G => l_non_empty_cont G
    | _ => true
    end.

  Definition l_precond L :=
    l_closed L && lguarded 0 L && l_non_empty_cont L.

  Lemma lne_open n G G' :
    l_non_empty_cont G -> l_non_empty_cont G' -> l_non_empty_cont (l_open n G' G).
  Proof.
    move=> NE1 NE2; move: NE1.
    elim/lty_ind2: G n=>//.
    - by move=>v n; rewrite /=; case: ifP=>//.
    - by move=> G Ih n /=; apply/Ih.
    - move=> a T C Ih n /=; case: C Ih=>//= K Ks Ih /andP-[NE_K ALL].
      have K_in: K \in K :: Ks by rewrite in_cons !eq_refl.
      rewrite (Ih K K_in n NE_K) /= {NE_K}.
      move: ALL=>/forallbP/forall_member/member_map-ALL.
      apply/forallbP/forall_member/member_map/member_map=>/=K' M.
      move: M (ALL _ M)=>/memberP-M {}ALL.
      have K'_in : K' \in K :: Ks by rewrite in_cons M orbT.
      by apply/(Ih _ K'_in n)/ALL.
  Qed.

  Lemma lne_unr n G : l_non_empty_cont G -> l_non_empty_cont (lunroll n G).
  Proof.
    elim: n G=>[//|n/=] Ih; case=>//= G NE.
    have: l_non_empty_cont (l_rec G) by [].
    by move=>/(lne_open 0 NE); apply/Ih.
  Qed.

  Definition l_expand' L :=
    match L with
    | l_msg a T Ks =>
      rl_msg a T (fun l : lbl => match find_cont Ks l with
                                 | Some (Ty, L0) => Some (Ty, l_expand L0)
                                 | None => None
                                 end)
    | _ => rl_end
    end.

  Lemma l_expand_once L : l_expand L = l_expand' (lunroll (lrec_depth L) L).
  Proof.
    by rewrite (rltyU (l_expand _)) /l_expand /l_expand'-rltyU-/l_expand.
  Qed.

  Lemma l_expand_unr L :
    lguarded 0 L ->
    l_closed L ->
    l_non_empty_cont L ->
    LUnroll L (l_expand L).
  Proof.
    move=>gG cG NE; rewrite l_expand_once.
    move: {-1}(l_expand' _) (erefl (l_expand' (lunroll (lrec_depth L) L))).
    move=>CG ECG; move: L CG {ECG gG cG NE}(conj ECG (conj gG (conj cG NE))).
    apply/paco2_acc=>r _ /(_ _ _ (conj erefl (conj _ (conj _ _))))-CIH.
    move=> G CG [<-]{CG} [gG][cG][NE].
    case: G cG gG NE.
    - move=>_ _ _ /=; by apply/paco2_fold; constructor.
    - by move=>V /lclosed_not_var/(_ V)/eqP/(_ erefl).
    - move=>G cG gG nE /=;apply/paco2_fold.
      constructor; right; have gG': lguarded 1 G by move: gG.
      rewrite (lguarded_recdepth (m:=0) gG' _ (l_rec G)) //.
      apply/CIH.
      by apply/l_guarded_unroll.
      by apply/lopen_closed.
      by apply/lne_open.
    - move=>F T C cG gG NE; apply/paco2_fold; constructor.
      + move=>l Ty; case: find_cont=>[[Ty0 L0]|]//; split=>[][G]//[->] _.
        * by exists (l_expand L0).
        * by exists L0.
      + move=> l Ty G CG FND; rewrite FND=>[][<-]; right.
        move: cG; rewrite /l_closed/==>/fsetUs_fset0/member_map-cG.
        move: gG; rewrite /==>/forallbP/forall_member-gG.
        move: NE=>/==>/andP-[NE_C]/forallbP/forall_member/member_map-NE.
        move: (find_member FND)=>MEM.
        rewrite l_expand_once.
        by apply/(CIH _ (gG _ MEM) (cG _ MEM) (NE _ MEM)).
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

  Definition look (E : {fmap role -> rl_ty}) p := odflt rl_end E.[? p]%fmap.

    Definition do_act_lt (L : rl_ty) A :=
    let: (mk_act a p q l t) := A in
    match L with
    | rl_msg a' q' Ks =>
      match Ks l with
      | Some (t', Lp) =>
        if (a == a') && (q == q') && (t == t')
        then Some Lp
        else None
      | None => None
      end
    | _ => None
    end%fmap.

    Definition run_act_lt (L : rl_ty) A := odflt L (do_act_lt L A).

    Definition do_act (P : renv) A :=
      let: (mk_act a p q l t) := A in
      match do_act_lt (look P p) A with
      | Some Lp => Some (P.[p <- Lp]%fmap)
      | None => None
      end.

  Lemma doact_send (E : renv) p q lb t KsL Lp :
    (look E p = rl_msg l_send q KsL) ->
    (KsL lb = Some (t, Lp)) ->
    exists E', (do_act E (mk_act l_send p q lb t) = Some E').
  Proof.
    move=>H1 H2; rewrite /do_act/do_act_lt H1 H2 !eq_refl/=.
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

  Lemma LUnroll_EqL L CL CL' : LUnroll L CL -> EqL CL CL' -> LUnroll L CL'.
  Proof.
    move=> H1 H2; move: L CL' {H1 H2 CL} (ex_intro (fun=>_) CL (conj H1 H2)).
    apply/paco2_acc=>r _ /(_ _ _ (ex_intro _ _ (conj _ _)))-CIH.
    move=> L CL [CL'][LU]EQ.
    move: LU EQ=>/(paco2_unfold l_unroll_monotone); case.
    - move=>/(paco2_unfold EqL_monotone); case E: _ _ / =>//.
      by apply/paco2_fold; constructor.
    - move=> G G' [/CIH-GU|//] /GU-H.
      by apply/paco2_fold; constructor; right.
    - move=> a p Ks C DOM ALL; move=>/(paco2_unfold EqL_monotone).
      case E: _ _ / =>[|a' p' CL1 CL2 DOM' EQ_ALL]//.
      move: E DOM' EQ_ALL=>[<-<-<-] DOM' E_ALL {a' p' CL1}.
      apply/paco2_fold; constructor; first by apply/(same_dom_trans DOM).
      move=>l Ty G iL Cl CCl; right.
      move: (dom DOM Cl)=>[LL]Cl'.
      move: (ALL _ _ _ _ Cl Cl')=>[UG|//].
      move: (E_ALL _ _ _ _ Cl' CCl)=>[EG|//].
      by apply/(CIH _ _ _ UG EG).
  Qed.

  Fixpoint n_rec d L :=
    match d with
    | 0 => L
    | d.+1 => l_rec (n_rec d L)
    end.

  Fixpoint n_open d n L :=
    match n with
    | 0 => L
    | m.+1 => l_open d (n_rec d.+1 (n_open d.+1 m L)) (n_open d.+1 m L)
    end.

  Fixpoint get_nr L :=
    match L with
    | l_rec L => get_nr L
    | _ => L
    end.

  Lemma nrec_comm d L : n_rec d (l_rec L) = n_rec d.+1 L.
  Proof. by elim: d =>//= n ->. Qed.

  Lemma nopen_rec_comm n L : n_open 0 n (l_rec L) = l_rec (n_open 1 n L).
  Proof.
    elim: n 0 L=>//= n Ih d L.
    rewrite Ih/= -Ih/= -/(n_rec d.+1 _) -/(n_rec d.+2 _).
    by rewrite Ih -/(n_rec d.+2 _) nrec_comm.
  Qed.

  Lemma lunroll_nopen L :
    lunroll (lrec_depth L) L = n_open 0 (lrec_depth L) (get_nr L).
  Proof.
    rewrite -{2}/(n_open 0 0 L) -{2}(@addn0 (lrec_depth L)); move: {2 4}0 => n.
    elim: L n=>//= L Ih n.
    rewrite nopen_rec_comm/= -/(n_open 0 (lrec_depth L + n).+1 _).
    by rewrite -/(n_open 0 n.+1 _); rewrite Ih addnS.
  Qed.

  Lemma nopen_var' m n L v : n_open m n L = l_var v -> L = l_var v.
  Proof.
    elim: n m=>//= n Ih m.
    case EQ: n_open=>[|v'||]//=; case: ifP=>// _ [EV].
    by move: EV EQ=>->{v'}/Ih.
  Qed.

  Lemma getnr_nonrec L : match get_nr L with
                         | l_rec _ => false
                         | _ => true
                         end.
  Proof. by elim: L. Qed.

  (* lbinds m (get_nr L) is the same as get_nr L = l_var m *)
  Lemma nopen_rec d n L L' :
    n_open d n (get_nr L) = l_rec L' ->
    exists m, l_binds m (get_nr L) /\ m < d + n.
  Proof.
    elim: n =>[|n Ih] //= in d L' *;
      first by move=> H; move: H (getnr_nonrec L)=>->.
    case EQ: (n_open d.+1 n (get_nr L)) => [|v|Lr|]//=.
    - case: ifP=>///eqP-EV; rewrite (nopen_var' EQ)/=EV =>{}EQ.
      exists d; rewrite eq_refl; split=>//.
      rewrite addnS; by apply/leq_addr.
    - move: (Ih _ _ EQ)=>[m][BND] LE _.
      by exists m; split=>//; rewrite addnS.
  Qed.

  (* l_open d L (n_rec m L') = n_rec m (l_open (d - m) L L') ? *)
  Lemma lopen_nrec d m L
    : l_open d L (n_rec m (l_var m)) = n_rec m (if d == 0 then L else l_var m).
  Proof.
    rewrite -{2 4}(add0n m) -{1}(add0n d); move: {-3}0=>n.
    elim: m=>[|m Ih]/= in n *.
    - case: (ifP (d == 0))=>[/eqP->|]; first by rewrite eq_refl.
      by case: ifP=>//; rewrite eqn_add2l eq_sym=>->.
    - by rewrite addnS -!addSn Ih.
  Qed.

  Lemma nrec_lrecdepthI L : L = n_rec (lrec_depth L) (get_nr L).
  Proof. by elim: L=>//= L<-. Qed.

  Lemma nrec_twice n m L : n_rec n (n_rec m L) = n_rec (n + m) L.
  Proof. by elim n=>//= {}n->. Qed.

  Lemma lopen_bound d n m L :
    m < d + n ->
    l_open d L (n_rec n (l_var m)) = n_rec n (l_var m).
  Proof.
    elim: n=>[|n Ih]//= in d *; last by rewrite addnS -addSn=>/Ih->.
    by rewrite addn0 ltn_neqAle=>/andP-[/negPf->].
  Qed.

  Lemma lunroll_inf Li Lr Li' :
    lunroll (lrec_depth Li) Li = l_rec Li' ->
    LUnroll Li Lr.
  Proof.
    rewrite lunroll_nopen=>/nopen_rec-[m]; rewrite add0n=>[][BND].
    rewrite {2}(nrec_lrecdepthI Li).
    move: (getnr_nonrec Li) BND; case: (get_nr Li)=>//= v _ /eqP->.
    move: (lrec_depth Li)=>d {v Li Li'}.
    move EQ: (n_rec d (l_var m))=>Li LT; move: {EQ LT}(conj EQ LT)=>H.
    move: (ex_intro (fun=>_) m (ex_intro (fun=>_) d H))=>{m d}H.
    move: Li Lr H; apply/paco2_acc=> r _.
    move=>/(_ _ _ (ex_intro _ _ (ex_intro _ _ (conj erefl _ ))))-CIH Li Lr.
    move=>[m][n][<-]{Li}; case: n=>//= n LE.
    apply/paco2_fold; constructor; move: LE; case: (boolP (n == m)).
    - move=>/eqP-> _; rewrite lopen_nrec eq_refl nrec_comm nrec_twice addSn.
      by right; apply/CIH; apply: leq_addr.
    - move=> H0 H1; move: {H0 H1} (conj H0 H1)=>/andP.
      rewrite eq_sym -ltn_neqAle => LE; rewrite lopen_bound //.
      by right; apply/CIH.
  Qed.

  Lemma do_act_works Li Lr A :
    LUnroll Li Lr -> LUnroll (run_act_l_ty Li A) (run_act_lt Lr A).
  Proof.
    rewrite /run_act_l_ty/run_act_lt/do_act_l_ty/do_act_lt/==>LU.
    case: A=> a _ q l t; move: ((LUnroll_ind (lrec_depth Li) Li Lr).1 LU)=>LU'.
    move: LU' LU.
    case EQ: (lunroll (lrec_depth Li) Li)=> [| v | Li' | a' p C].
    - by move=> /lunroll_end->.
    - by move=>/(paco2_unfold l_unroll_monotone); case F: _ _ /.
    - by move=>/= _ _; apply/(lunroll_inf _ EQ).
    - move=>/(paco2_unfold l_unroll_monotone).
      case F: _ _ / =>[||a0 p0 K0 C0 DOM UNR]//.
      move: F DOM UNR=>[<-<-<-] DOM UNR{a0 p0 K0 EQ}.
      case EQ: find_cont=>[[Ty L]|]//; last by rewrite (dom_none DOM EQ).
      move: (dom DOM EQ)=>[{}Lr] EQ'; rewrite EQ'/=.
      case: (boolP ((a == a') && (q == p) && (t == Ty)))=>//= _ _.
      by move: (UNR _ _ _ _ EQ EQ')=>[].
  Qed.

  Open Scope fmap_scope.
  (** lstep a Q P Q' P' is the 'step' relation <P, Q> ->^a <P', Q'> in Coq*)
  Inductive lstep : act -> renv * qenv -> renv * qenv -> Prop :=
  | ls_send t p q lb (P P' : renv) (Q Q' : qenv) :
      Q' == enq Q (p, q) (lb, t) ->
      do_act P (mk_act l_send p q lb t) = Some P' ->
      lstep (mk_act l_send p q lb t) (P, Q) (P', Q')
  | ls_recv t p q lb (P P' : renv) (Q Q' : qenv) :
      deq Q (p, q) == Some ((lb, t), Q') ->
      do_act P (mk_act l_recv q p lb t) = Some P' ->
      lstep (mk_act l_recv q p lb t) (P, Q) (P', Q')
  .
  Derive Inversion lstep_inv with (forall A P P', lstep A P P') Sort Prop.

  Definition runnable (A : act) (P : renv * qenv) : bool :=
    match do_act P.1 A with
    | Some _ =>
      let: mk_act a p q l t := A in
      match a with
      | l_send => true
      | l_recv =>
        match deq P.2 (q, p) with
        | Some ((l', t'), Q) => (l == l') && (t == t')
        | None => false
        end
      end
    | None => false
    end.

  Lemma lstep_runnable A P P' : lstep A P P' -> runnable A P.
  Proof.
    by case=> Ty F T l {P P'}E E' Q Q' /eqP-QFT /=; case LOOK: look=>[|a p C]//;
       case Cl: (C l)=>[[Ty' L]|]//; case: ifP=>//EQ _;
       rewrite /runnable/= LOOK Cl EQ // QFT !eq_refl.
  Qed.

  Lemma lstep_eq A P P0 P1 : lstep A P P0 -> lstep A P P1 -> P0 = P1.
  Proof.
    case=>Ty0 F0 T0 l0 {P P0}E E0 Q Q0 /eqP-QFT/=; case LOOK: look=>[|a p C]//;
    case Cl: (C l0)=>[[Ty' L]|]//; case: ifP=>//EQ [<-];
    elim/lstep_inv =>// _ Ty1 F1 T1 l1 E' E1 Q' Q1 /eqP-QFT'/= ACT EQ1 EQ2 EQ3;
    move: EQ1 EQ2 EQ3 ACT QFT QFT'=>[->->->->] [->->] _ {F1 T1 l1 Ty1 E' Q' P1};
    rewrite LOOK Cl EQ=>[][<-]->.
    - by move=>->.
    - by move=>[->].
  Qed.

  Definition do_queue (Q : qenv) (A : act) : qenv :=
    match A with
    | mk_act l_send F T l Ty => enq Q (F, T) (l, Ty)
    | mk_act l_recv F T l Ty =>
      match deq Q (T, F) with
      | Some (_, Q') => Q'
      | None => Q
      end
    end.

  (* Attempts to run a step, does nothing if it cannot run *)
  Definition run_step (A : act) (P : renv * qenv) : renv * qenv :=
    match do_act P.1 A with
    | Some E' => (E', do_queue P.2 A)
    | _ => P
    end.

  (* Lemma run_step 'makes sense' *)
  Lemma run_step_sound A P : runnable A P -> lstep A P (run_step A P).
  Proof.
    case: P => E Q.
    rewrite /runnable /=; case E_doact: (do_act _ _)=>[E'|//].
    case: A E_doact=> [[|] p q l t E_doact]/=.
    - by move=> _; rewrite /run_step E_doact; constructor=>//.
    - case E_deq: (deq _ _) =>[[[l' t'] Q']|//].
      case: (boolP ((l == l') && _)) =>[/andP-[/eqP-ll' /eqP-tt']|//] _.
      move: ll' tt' E_deq =><-<- E_deq.
      rewrite /run_step E_doact /= E_deq.
        by constructor =>//; first by apply/eqP.
  Qed.

  Lemma run_step_compl A P P' : lstep A P P' -> P' = run_step A P.
  Proof.
    by move=> ST; move: (lstep_runnable ST)=>/run_step_sound/(lstep_eq ST).
  Qed.

  Definition rel_trc := trace act -> renv*qenv -> Prop.
  Inductive l_lts_ (r : rel_trc) : rel_trc :=
  | lt_end E :
      (forall p, look E p = rl_end) ->
      @l_lts_ r (tr_end _) (E, [fmap])
  | lt_next a t P P' :
      lstep a P P' ->
      r t P' ->
      @l_lts_ r (tr_next a t) P.
  Hint Constructors l_lts_.
  Lemma l_lts_monotone : monotone2 l_lts_.
  Proof. pmonauto. Qed.

  Definition l_lts t L := paco2 l_lts_ bot2 t L.
  Derive Inversion llts_inv with (forall tr G, l_lts tr G) Sort Prop.

  Definition rty_trc := trace act -> rl_ty -> Prop.
  Inductive l_trc_ (p : role) (r : rty_trc) : rty_trc :=
  | l_trc_end : l_trc_ p r (tr_end _) rl_end
  | l_trc_msg A TR L L' :
      subject A == p -> do_act_lt L A = Some L' ->
      r TR L' ->
      l_trc_ p r (tr_next A TR) L
  .
  Lemma l_trc_monotone p : monotone2 (l_trc_ p).
  Admitted.

  Definition l_trc p t L := paco2 (l_trc_ p) bot2 t L.

  Definition trc_rel := trace act -> trace act -> Prop.
  Inductive subtrace_ (p : role) (r : trc_rel) : trc_rel :=
  | subtrace_end : subtrace_ p r (tr_end _) (tr_end _)
  | subtrace_skip A TRp TR :
      subject A != p ->
      r TRp TR ->
      subtrace_ p r TRp (tr_next A TR)
  | subtrace_msg A TRp TR :
      subject A == p ->
      r TRp TR ->
      subtrace_ p r (tr_next A TRp) (tr_next A TR)
  .
  Lemma subtrace_monotone p : monotone2 (subtrace_ p).
  Admitted.
  Definition subtrace p T0 T1 := paco2 (subtrace_ p) bot2 T0 T1.

  Lemma ltrc_sound p E Tp T
    : l_trc p Tp (look E.1 p) -> l_lts T E -> subtrace p Tp T.
  Admitted.

  (*
    project G p == Some L ->
    il_trc p Tp L ->
    g_accepts T G ->
    subtrace p Tp T.
   *)

  (*
    project G p == Some L ->
    of_lt P L ->
    p_accepts p Tp         P ->
    g_accepts   T          G ->
    subtrace  p (erase Tp) T.
   *)

End Semantics.

Hint Constructors EqL_.
Hint Resolve EqL_monotone.
Hint Resolve EqL_refl.

Notation renv := {fmap role -> rl_ty}.
Notation qenv := {fmap role * role -> seq (lbl * mty) }.
Notation cfg := (renv * qenv)%type.
