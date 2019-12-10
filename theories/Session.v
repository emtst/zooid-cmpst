From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.Atom.
Require Import MPST.Role.
Require Import MPST.Forall.
Require Import MPST.LNVar.
Require Import MPST.Actions.

Section Session.

  Inductive s_ty :=
  | s_end
  | s_var (v : rvar)
  | s_rec (S : s_ty)
  | s_msg (a: l_act) (K : seq (lbl * (mty * s_ty))).

  Open Scope mpst_scope.

  Fixpoint eq_sty x y :=
    match x, y with
    | s_end, s_end => true
    | s_var x, s_var y => x == y
    | s_rec x, s_rec y => eq_sty x y
    | s_msg a1 Ks1, s_msg a2 Ks2
      => (a1 == a2)
           && (fix eqK Ks1 Ks2 :=
                 match Ks1, Ks2 with
                 | [::], [::] => true
                 | K1::Ks1, K2::Ks2 =>
                   (K1.lbl == K2.lbl)
                     && (K1.mty == K2.mty)
                     && eq_sty K1.cnt K2.cnt && eqK Ks1 Ks2
                 | _, _ => false
                 end) Ks1 Ks2
    (* all2 (fun l r => (l.1 == r.1) && eq_lty l.2 r.2) K1 K2 *)
    | _, _ => false
    end.

  Definition eq_salt (l r : lbl * (mty * s_ty)) :=
    (l.lbl == r.lbl) && (l.mty == r.mty) && eq_sty l.cnt r.cnt.

  Lemma eq_smsg_all a1 a2 K1 K2 :
    eq_sty (s_msg a1 K1) (s_msg a2 K2) = (a1 == a2) && all2 eq_salt K1 K2.
  Proof.
    rewrite /=; case: eqP=>[/=_{a1 a2}|//]; move: K1 K2.
    by elim=>//[[l1 [t1 L1]] K1] Ih; case=>//[[l2 [t2 L2]] K2]/=; rewrite Ih.
  Qed.

  Lemma sty_eqP : Equality.axiom eq_sty.
  Proof.
    rewrite /Equality.axiom; fix Ih 1 => x y.
    case: x => [|v|L|a K];
       case: y =>[|v'|L'|a' K']; try (by constructor).
    + by rewrite /eq_sty; case: eqP=>[->|F]; constructor=>//[[/F]].
    + by rewrite /=; case: Ih=>[->|F]; constructor=>//[[/F]].
    + rewrite eq_smsg_all/=; case: eqP=>[<-{a'}|F]/=; [|by constructor=>[[/F]]].
      elim: K K'=>[|[l [t L]] K IhK]; case=>[|[l' [t' L']]K']/=; try (by constructor).
      rewrite {1}/eq_salt/=; do 2 (case: eqP=>[<-|F];[|constructor=>[[/F]]//]).
      case: Ih=>[<-|F];[|constructor=>[[/F]]//].
      by case: IhK=>[[]<-|F]; constructor=>//[[]]H; apply: F; rewrite H.
  Qed.

  Definition sty_eqMixin := EqMixin sty_eqP.
  Canonical sty_eqType := Eval hnf in EqType s_ty sty_eqMixin.

  Fixpoint s_open (d : nat) (S2 : s_ty) (S1 : s_ty) :=
    match S1 with
    | s_end => S1
    | s_var v => Rvar.open s_var d S2 v
    | s_rec s => s_rec (s_open d.+1 S2 s)
    | s_msg a K => s_msg a [seq (lS.lbl, (lS.mty, s_open d S2 lS.cnt)) | lS <- K]
    end.
  Notation sfv a := (s_var (Rvar.fv a)).
  Notation sbv n := (s_var (Rvar.bv n)).
  Notation "{ k '~>' v } s":= (s_open k v s) (at level 30, right associativity).
  Notation "L '^' v":= (s_open 0 (sfv v) L) (at level 30, right associativity).

  Fixpoint s_close (v : atom) (d : nat) (L1 : s_ty) :=
    match L1 with
    | s_end => L1
    | s_var lv => s_var (Rvar.close v d lv)
    | s_rec L => s_rec (s_close v d.+1 L)
    | s_msg a K => s_msg a [seq (lL.lbl, (lL.mty, s_close v d lL.cnt)) | lL <- K]
    end.
  Notation "{ k '<~' v } L":= (s_close v k L) (at level 30, right associativity).

  Fixpoint s_fvar (L : s_ty) : {fset atom} :=
    match L with
    | s_end => fset0
    | s_var v => Rvar.fvar v
    | s_rec L => s_fvar L
    | s_msg _ K => fsetUs [seq s_fvar lL.cnt | lL <- K]
    end.

  Fixpoint s_fbvar (d : nat) (L : s_ty) : {fset nat} :=
    match L with
    | s_end => fset0
    | s_var v => Rvar.fbvar d v
    | s_rec L => s_fbvar d.+1 L
    | s_msg _ K => fsetUs [seq s_fbvar d lL.cnt | lL <- K]
    end.

  Lemma sty_ind :
    forall (P : s_ty -> Prop),
      P s_end ->
      (forall v, P (s_var v)) ->
      (forall s, P s -> P (s_rec s)) ->
      (forall a K, Forall (fun lS => P lS.cnt) K -> P (s_msg a K)) ->
      forall s : s_ty, P s.
  Proof.
    move => P P_end P_var P_rec P_msg.
    fix Ih 1; case=>[|v|L|a K].
    + by apply: P_end.
    + by apply: P_var.
    + by apply: P_rec.
    + by apply: P_msg; elim: K.
  Qed.

  Lemma s_open_close X L n : X \notin s_fvar L -> {n <~ X}{n ~> sfv X}L = L.
  Proof.
    elim/sty_ind: L n=>[|v|L Ih|a K Ih] n /=Fv//;
      try (by rewrite Ih).
    + by move: Fv; rewrite Rvar.open_fun/= =>H; rewrite Rvar.open_close.
    + move: Ih=>/Fa_lift/(_ n)-Ih; move: Fv => /notin_unions/Fa_map-Fv.
      move: (Fa_app (Fa_conj Ih Fv)) => {Ih Fv}Ih; rewrite -map_comp /comp/=.
      by elim: K Ih=>// [[l [t L]] K Ih/= [-> /Ih-[->]]].
  Qed.

  Lemma s_close_open n X L : n \notin s_fbvar 0 L -> {n ~> sfv X}{n <~ X}L = L.
  Proof.
    move: {1 3}n (add0n n)=>n0; elim/sty_ind: L 0 n =>///=.
    - by move=>v n n1;rewrite addnC Rvar.open_fun=><-H;rewrite Rvar.close_open.
    - by move=>G Ih n n1 Eq/= H; rewrite (Ih n.+1 n1.+1) // -Eq.
    - move=> a K /Fa_lift-Ih n n1 Eq /notin_unions/Fa_map-H.
      move:Ih=>/(_ n)/Fa_lift/(_ n1)/Fa_lift/(_ Eq)/Fa_conj/( _ H)/Fa_app-Ih{H}.
      congr s_msg; rewrite -map_comp/comp/=; elim: K Ih=>[//|[l[t S]] K Ih /=].
      by move=>[->/Ih->].
  Qed.

  Fixpoint depth_sty L :=
    match L with
    | s_end
    | s_var _ => 0
    | s_rec L => (depth_sty L).+1
    | s_msg _ K  => (maximum [seq depth_sty l.cnt | l <- K]).+1
    end.

  Lemma s_depth_open L X : depth_sty L = depth_sty (L^X).
  Proof.
    move: 0; elim/sty_ind: L=>/=//.
    + by move=>v n; rewrite Rvar.open_fun.
    + by move=> L Ih n; rewrite (Ih n.+1).
    + move=> a K Ih n; rewrite -map_comp /comp/=.
      by move: Ih => /Fa_lift/(_ n)/Fa_map_eq<-.
  Qed.

  Lemma sty_ind1 :
    forall (P : s_ty -> Prop),
      P s_end ->
      (forall v, P (s_var v)) ->
      (forall s, (forall X (A : {fset atom}), X \notin A -> P (s ^ X)) ->
                 P (s_rec s)) ->
      (forall a Ks, (forall K, K \in Ks -> P K.cnt) -> P (s_msg a Ks)) ->
      forall s : s_ty, P s.
  Proof.
    move => P P_end P_var P_rec P_msg L.
    move: {-1}(depth_sty L) (leqnn (depth_sty L))=> n; move: n L; elim.
    + by case.
    + move=>n Ih; case=>/=//.
      - by move=>L D; apply:P_rec=>X S _;apply: Ih;rewrite -(s_depth_open L X).
      - move=> a K D;apply: P_msg =>L /(map_f (fun X => depth_sty X.cnt)).
        move=>/in_maximum_leq-/=dG; move: (leq_trans dG D)=>{dG} {D}.
        by apply: Ih.
  Qed.

  Fixpoint dual (L : s_ty) : s_ty :=
    match L with
    | s_end => s_end
    | s_var v => s_var v
    | s_rec s => s_rec (dual s)
    | s_msg a K => s_msg (dual_act a) [seq (x.lbl, (x.mty, dual x.cnt)) | x <- K]
    end.

  Lemma dualK s : dual (dual s) = s.
  Proof.
    elim/sty_ind: s=>[|v|s Ih|a K Ih]//; try (by rewrite /=Ih).
    - rewrite /= -map_comp /comp/= dual_actK.
      by elim: K Ih=>[//|[l [t s]] K Ihl /= [-> /Ihl-[->]]].
  Qed.

  Definition is_dual (s1 s2 : s_ty) : bool := s1 == dual s2.

  Lemma isdual_sym (s1 s2 : s_ty) : is_dual s1 s2 -> is_dual s2 s1.
  Proof. by move=>/eqP->; rewrite /is_dual dualK. Qed.

  Lemma is_dual_var v : is_dual (s_var v) (s_var v).
  Proof. by rewrite /is_dual/dual. Qed.

  Lemma isdualC (s1 s2 : s_ty) : is_dual s1 s2 = is_dual s2 s1.
  Proof.
    move: {-1}(is_dual s1 s2) (eq_refl (is_dual s1 s2)) => D.
    rewrite /is_dual; case: D=>[/eqP/eqP->|].
    - by rewrite dualK eq_refl.
    - move=>/eqP; rewrite (rwP negPf)=> H; apply/esym; move: H; apply: contraTF.
      by rewrite negbK=>/eqP->; rewrite dualK.
  Qed.

  Lemma dualI : injective dual.
  Proof. by move=>x1 x2; rewrite -{2}(dualK x1) -{2}(dualK x2)=>->. Qed.
End Session.