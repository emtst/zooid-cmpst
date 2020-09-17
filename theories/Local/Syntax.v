From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.

From Paco Require Import paco paco2.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.Common.

Section Syntax.
Unset Elimination Schemes.
Inductive l_ty :=
| l_end
| l_var (v : nat)
| l_rec (L : l_ty)
| l_msg (a : l_act) (r : role) (Ks : seq (lbl * (mty * l_ty)))
.
Set Elimination Schemes.

Definition ilook (E : seq (role * l_ty)) p := odflt l_end (find_cont E p).

Fixpoint partsL (G : l_ty) :=
  match G with
  | l_end
  | l_var _ => [::]
  | l_rec G => partsL G
  | l_msg a p Ks => p::flatten [seq partsL K.2.2 | K <- Ks]
  end.

Lemma lty_ind :
  forall (P : l_ty -> Prop),
    P l_end ->
    (forall v, P (l_var v)) ->
    (forall G, P G -> P (l_rec G)) ->
    (forall a p Ks, Forall (fun K => P K.2.2) Ks -> P (l_msg a p Ks)) ->
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
  | l_msg _ _ Ks => (foldr maxn 0 [seq depth_lty K.2.2 | K <- Ks]).+1
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
                 (K1.1 == K2.1)
                   && (K1.2.1 == K2.2.1)
                   && eq_lty K1.2.2 K2.2.2
                   && eqK Ks1 Ks2
               | _, _ => false
               end) Ks1 Ks2
  | _, _ => false
  end.

Definition eq_lalt (l r : lbl * (mty * l_ty)) :=
  (l.1 == r.1) && (l.2.1 == r.2.1) && eq_lty l.2.2 r.2.2.

Lemma eqmsg_all a1 a2 r1 r2 K1 K2 :
  eq_lty (l_msg a1 r1 K1) (l_msg a2 r2 K2) =
  (a1 == a2) && (r1 == r2) && all2 eq_lalt K1 K2.
Proof.
  rewrite /=; do 2 (case: eqP=>///= _); move: K1 K2 {r1 r2 a1 a2}.
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

Lemma in_maximum_leq v l: v \in l -> v <= foldr maxn 0 l.
Proof.
  elim: l=>//v' l Ih; rewrite in_cons=>/orP-[/eqP<-|]/=.
  + by apply: leq_maxl.
  + by move=>/Ih{Ih}; move: (foldr _ _ _) => k {l}; rewrite leq_max orbC=>->.
Qed.

Lemma l_ty_ind :
  forall (P : l_ty -> Prop),
    P l_end ->
    (forall v, P (l_var v)) ->
    (forall L, P L -> P (l_rec L)) ->
    (forall a p Ks, (forall K, K \in Ks -> P K.2.2) -> P (l_msg a p Ks)) ->
    forall l : l_ty, P l.
Proof.
  move => P P_end P_var P_rec P_msg L.
  move: {-1}(depth_lty L) (leqnn (depth_lty L))=> n; move: n L; elim.
  + by case.
  + move=>n Ih; case=>/=//.
  - by move=>L D; apply:P_rec; apply: Ih.
  - move=> a r Ks D;apply: P_msg=>K /(map_f (fun X => depth_lty X.2.2)).
    move=>/in_maximum_leq-/=dG; move: (leq_trans dG D)=>{dG} {D}.
      by apply: Ih.
Qed.

Fixpoint l_shift n d (L : l_ty) :=
  match L with
  | l_end => l_end
  | l_var v => if v >= d then l_var (n + v) else L
  | l_msg a p Ks => l_msg a p [seq (K.1, (K.2.1, l_shift n d K.2.2)) | K <- Ks]
  | l_rec L => l_rec (l_shift n d.+1 L)
  end.

Fixpoint l_open (d : nat) (L2 : l_ty) (L1 : l_ty) :=
  match L1 with
  | l_end => L1
  | l_var v => if v == d then l_shift d 0 L2 else L1
  | l_rec L => l_rec (l_open d.+1 L2 L)
  | l_msg a p Ks =>
    l_msg a p [seq (K.1, (K.2.1, l_open d L2 K.2.2)) | K <- Ks]
  end.
Notation "{ k '~>' v } L":= (l_open k v L) (at level 30, right associativity).
Notation "L '^' v":= (l_open 0 (l_var v) L) (at level 30, right associativity).

Lemma open_notvar n L L' :
  (forall v : nat, L != l_var v) ->
  (forall v : nat, l_open n L' L != l_var v).
Proof. by case: L=>//v /(_ v)/eqP. Qed.

Lemma l_open_msg_rw d L2 a r Ks:
 l_open d L2 (l_msg a r Ks)
 = l_msg a r [seq (K.1, (K.2.1, l_open d L2 K.2.2)) | K <- Ks].
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

Fixpoint l_fidx (d : nat) (L : l_ty) : seq nat :=
  match L with
  | l_end => [::]
  | l_var v => if v >= d then [:: v - d] else [::]
  | l_rec L => l_fidx d.+1 L
  | l_msg _ _ K => flatten [seq l_fidx d lL.2.2 | lL <- K]
  end.

Definition l_closed (L : l_ty) := l_fidx 0 L == [::].

Lemma lfbvar_next n G :
  l_fidx n G == [::] ->
  l_fidx n.+1 G = [::].
Proof.
  elim: G n=>[//|v|G Ih|p q Ks Ih] n/=.
  - case: v=>//= m H; case: ifP=>// n_m; move: H.
    by move: (leq_trans (leqnSn n) n_m)=>->.
  - by apply: Ih.
  - rewrite flatten_eq_nil member_map=>H; apply/eqP.
    rewrite flatten_eq_nil member_map=> K /memberP-M.
    by move: M (Ih K M n)=>/memberP-M /(_ (H K M))=>->.
Qed.

Lemma lfbvar_gt n m G :
  n <= m ->
  l_fidx n G == fset0 ->
  l_fidx m G = fset0.
Proof.
  move=> LE H; move: LE; elim: m=>[|m Ih]//; first by case: n H=>///eqP.
  move: H; case: (boolP (n == m.+1))=>[/eqP->/eqP//|NE _ LE].
  apply/lfbvar_next/eqP/Ih; move: (conj NE LE)=>/andP.
  by rewrite -ltn_neqAle.
Qed.

Lemma lshift_closed n d G :
  l_fidx d G == fset0 ->
  l_shift n d G = G.
Proof.
  elim: G=> [| v | L Ih | a p Ks Ih]//= in d *.
  { (* var *)
    by case: ifP=>//.
  }
  { (* rec *)
    by move=>H; congr l_rec; apply/Ih.
  }
  { (* msg *)
    move=>/flatten_eq_nil/member_map/(_ _ ((rwP (memberP _ _)).2 _))-H.
    congr l_msg; rewrite -{2}(map_id Ks); apply/eq_in_map=>K IN.
    by rewrite (Ih _ IN _ (H _ IN)) -!surjective_pairing.
  }
Qed.

Lemma lopen_closed G :
  l_closed (l_rec G) ->
  l_closed (l_open 0 (l_rec G) G).
Proof.
  rewrite/l_closed/==>G_fbv.
  have: l_fidx 0 (l_rec G) == fset0 by [].
  move: (l_rec G) => G' G'0.
  elim: G 0 G_fbv=>[//|v|G Ih|p q Ks Ih] n /=.
  - move=> H; case: ifP=>[|/=].
    + move=> _; rewrite (lshift_closed n G'0); apply/eqP.
      by move: G'0; apply/lfbvar_gt.
    + case: ifP=>// LE /(rwP negPf)-NE; move: (conj NE LE)=>/andP.
      by rewrite eq_sym -ltn_neqAle=>LT; move: H; rewrite LT.
  - by apply: (Ih n.+1); rewrite lfbvar_next.
  - rewrite -map_comp/comp/=; move=>/flatten_eq_nil/member_map-H.
    apply/flatten_eq_nil/member_map=>K /memberP-M.
    by apply: Ih=>//; apply: H; apply/memberP.
Qed.

Fixpoint lguarded d L :=
  match L with
  | l_end => true
  | l_var v => v >= d
  | l_rec L => lguarded d.+1 L
  | l_msg _ _ Ks => all (fun K => lguarded 0 K.2.2) Ks
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
  | l_msg _ _ Ks => all (fun K => lguarded' K.2.2) Ks
  end.

Lemma lguarded_next n G : lguarded n.+1 G = ~~ l_binds n G && lguarded n G.
Proof. by elim: G n=>//= v n; rewrite ltn_neqAle eq_sym. Qed.

Lemma lguarded_binds G : lguarded 0 G = lguarded' G.
Proof.
  elim: G=>[||G|_ _ Ks Ih]//=; first by move=><-;apply/lguarded_next.
  elim: Ks Ih=>[//|K Ks Ih']/= Ih; rewrite Ih ?in_cons ?eq_refl //.
  by rewrite Ih' // => K' H; apply/Ih; rewrite in_cons orbC H.
Qed.

Lemma lguarded_rec d L
  : lguarded d (l_rec L) -> forall s, s <= d -> ~~ l_binds s L.
elim: L=>[|v|L /= Ih|a p Ks Ih]// in d *.
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
  elim: G=>[|n|G Ih|p q Ks Ih]//= in d m *.
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
  elim: G =>[|n|G Ih|p q Ks Ih]// in dG dG' *.
  - by move=> m /leq_trans-H /= /H->.
  - by move=> n ndG' /=; apply/Ih.
Qed.

Lemma lclosed_not_var G :
  l_closed G ->
  forall v, G != l_var v.
Proof.
  rewrite /l_closed.
  by case: G=>//= v.
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
  elim: G=>[|n|G Ih|p q Ks Ih]//= in d1 d2 *.
  - case: ifP=>// _ gG cG; rewrite (lshift_closed _ cG)=>_.
    by apply/(lguarded_depth_gt _ gG).
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
  elim: G=>[|n|G Ih|p q Ks Ih]//= in d d' *.
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
  elim: L=>[|v|L Ih|a p KS Ih]//= in n *; move=> END.
  by rewrite Ih.
Qed.

Lemma keep_unrolling L :
  l_isend L -> exists m, l_end = lunroll m L.
Proof.
  elim: L=>[||L Ih|]//; [move=>_| move=>/=END; move:(Ih END)=>[n U]].
  - by exists 0.
  - by exists n.+1=>/=; rewrite (isend_open 0 _ END).
Qed.

Lemma l_closed_no_binds_aux m n L: m <= n -> l_fidx m L == fset0
  -> l_binds n L = false.
Proof.
elim: L m n; rewrite //=.
+ move=> v m n le; case: ifP=>//.
  by move=> lefalse; elim; apply: ltn_eqF;
    apply: (leq_trans _ le); move: (negbT lefalse); rewrite-ltnNge //=.
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
  rewrite (lshift_closed _ closed).
  move: (@l_closed_no_binds m _ closed); rewrite /l_binds; move =>->.
  by move: (negbTE neq).
+ by move=> L IH m n L1 neq closed; rewrite //=; apply: IH.
+ by [].
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
  : l_open d L (n_rec m (l_var m)) =
    n_rec m (if d == 0 then l_shift (d + m) 0 L else l_var m).
Proof.
  rewrite -{2 5} (add0n m) -{1 3}(add0n d); move: {-3 5}0=>n.
  elim: m=>[|m Ih]/= in n *.
  - case: (ifP (d == 0))=>[/eqP->|]; first by rewrite eq_refl !addn0.
    by case: ifP=>//; rewrite eqn_add2l eq_sym=>->.
  - by rewrite !addnS -!addSn Ih.
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

Lemma lshift_nrec d r m n :
  n < r + m ->
  l_shift d r (n_rec m (l_var n)) = n_rec m (l_var n).
Proof.
  elim: m=> [|m Ih]//= in r *; first by rewrite addn0 ltnNge=>/negPf->.
  by rewrite addnS -addSn/==>/Ih->.
Qed.

End Syntax.
