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

  Inductive l_ty :=
  | l_end
  | l_var (v : rvar)
  | l_rec (L : l_ty)
  | l_msg (a : l_act) (r : role) (Ks : seq (lbl * (mty * l_ty)))
  .

  Notation lfv a := (l_var (fv a)).
  Notation lbv n := (l_var (bv n)).

  Open Scope mpst_scope.

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
    | l_var v => open l_var d L2 v
    | l_rec L => l_rec (l_open d.+1 L2 L)
    | l_msg a p Ks =>
      l_msg a p [seq (K.lbl, (K.mty, l_open d L2 K.cnt)) | K <- Ks]
    end.
  Notation "{ k '~>' v } L":= (l_open k v L) (at level 30, right associativity).
  Notation "L '^' v":= (l_open 0 (lfv v) L) (at level 30, right associativity).

  Fixpoint l_close (v : atom) (d : nat) (L1 : l_ty) :=
    match L1 with
    | l_end => L1
    | l_var lv => l_var (close v d lv)
    | l_rec L => l_rec (l_close v d.+1 L)
    | l_msg a p Ks =>
      l_msg a p [seq (K.lbl, (K.mty, l_close v d K.cnt)) | K <- Ks]
    end.
  Notation "{ k '<~' v } L":= (l_close v k L) (at level 30, right associativity).

  Lemma unzip2_lift A B C (f : B -> C) (K : seq (A * B)) :
    [seq f x | x <- unzip2 K] = unzip2 [seq (x.1, f x.2) | x <- K].
  Proof. by rewrite /unzip2 -!map_comp /comp. Qed.

  Lemma unzip1_map2 A B C (f : B -> C) (K : seq (A * B)) :
    unzip1 K = unzip1 [seq (x.1, f x.2) | x <- K].
  Proof. by rewrite /unzip1 -map_comp /comp. Qed.

  Lemma map2_zip A B C (f : B -> C) (K : seq (A * B)) :
    zip (unzip1 K) [seq f x | x <- unzip2 K] = [seq (x.1, f x.2) | x <- K].
  Proof. by rewrite unzip2_lift (unzip1_map2 f) zip_unzip. Qed.

  (*
  Lemma lclose_send_zip v d p K :
    l_close v d (l_send p K)
    = l_send p (zip (unzip1 K) (zip (unzip1 (unzip2 K)) [seq l_close v d x | x <- unzip2 (unzip2 K)])).
  Proof. by rewrite /= unzip2_lift (unzip1_map2 (l_close v d)) zip_unzip. Qed.

  Lemma lclose_sel_zip v d p K :
    l_close v d (l_sel p K)
    = l_sel p (zip (unzip1 K) [seq l_close v d x | x <- unzip2 K]).
  Proof. by rewrite /= unzip2_lift (unzip1_map2 (l_close v d)) zip_unzip. Qed.
   *)

  Fixpoint l_fvar (L : l_ty) : {fset atom} :=
    match L with
    | l_end => fset0
    | l_var v => fvar v
    | l_rec L => l_fvar L
    | l_msg _ _ K => fsetUs [seq l_fvar lL.cnt | lL <- K]
    end.

  Fixpoint l_fbvar (d : nat) (L : l_ty) : {fset nat} :=
    match L with
    | l_end => fset0
    | l_var v => fbvar d v
    | l_rec L => l_fbvar d.+1 L
    | l_msg _ _ K => fsetUs [seq l_fbvar d lL.cnt | lL <- K]
    end.

  Lemma l_open_close X L n : X \notin l_fvar L -> {n <~ X}{n ~> lfv X}L = L.
  Proof.
    elim/lty_ind: L n=>[|v|L Ih|a r K Ih] n /=Fv//;
      try (by rewrite Ih).
    + by move: Fv; rewrite open_fun/= =>H; rewrite open_close.
    + move: Ih=>/Fa_lift/(_ n)-Ih; move: Fv => /notin_unions/Fa_map-Fv.
      move: (Fa_app (Fa_conj Ih Fv)) => {Ih Fv}Ih; rewrite -map_comp /comp/=.
      by elim: K Ih=>// [[l [t L]] K Ih/= [-> /Ih-[->]]].
  Qed.

  Lemma l_close_open n X L : n \notin l_fbvar 0 L -> {n ~> lfv X}{n <~ X}L = L.
  Proof.
    move: {1 3}n (add0n n)=>n0; elim/lty_ind: L 0 n =>///=.
    - by move=>v n n1;rewrite addnC open_fun=><-H;rewrite close_open.
    - by move=>G Ih n n1 Eq/= H; rewrite (Ih n.+1 n1.+1) // -Eq.
    - move=> a r K /Fa_lift-Ih n n1 Eq /notin_unions/Fa_map-H.
      move:Ih=>/(_ n)/Fa_lift/(_ n1)/Fa_lift/(_ Eq)/Fa_conj/( _ H)/Fa_app-Ih{H}.
      congr l_msg; rewrite -map_comp/comp/=.
      by elim: K Ih => [// | [l [t L]] K/= IhL [-> /IhL->]].
  Qed.

  Lemma l_depth_open L X : depth_lty L = depth_lty (L^X).
  Proof.
    move: 0; elim/lty_ind: L=>/=//.
    + by move=>v n; rewrite open_fun.
    + by move=> L Ih n; rewrite (Ih n.+1).
    + move=> _ _ K Ih n; rewrite -map_comp /comp/=.
      by move: Ih => /Fa_lift/(_ n)/Fa_map_eq<-.
  Qed.

  Lemma lty_ind1 :
    forall (P : l_ty -> Prop),
      P l_end ->
      (forall v, P (l_var v)) ->
      (forall L, (forall X (s : {fset atom}), X \notin s -> P (L ^ X)) ->
                 P (l_rec L)) ->
      (forall a p Ks, (forall K, K \in Ks -> P K.cnt) -> P (l_msg a p Ks)) ->
      forall l : l_ty, P l.
  Proof.
    move => P P_end P_var P_rec P_msg L.
    move: {-1}(depth_lty L) (leqnn (depth_lty L))=> n; move: n L; elim.
    + by case.
    + move=>n Ih; case=>/=//.
      - by move=>L D; apply:P_rec=>X S _;apply: Ih;rewrite -(l_depth_open L X).
      - move=> a r Ks D;apply: P_msg=>K /(map_f (fun X => depth_lty X.cnt)).
        move=>/in_maximum_leq-/=dG; move: (leq_trans dG D)=>{dG} {D}.
        by apply: Ih.
  Qed.
End Syntax.

Section Semantics.

  Definition PEnv := seq (role * l_ty).

  Definition act_lty a L :=
    if subject a == L.1
    then
      let L1 := match L.2 with
                | l_rec L' => l_open 0 (l_rec L') L'
                | _ => L.2
                end
      in match a, L1 with
         | a_send p q lb t, l_msg l_send q' K =>
           if q == q'
           then match lookup lb K with
                | Some (t', s) => if t == t' then Some s else None
                | None => None
                end
           else None
         | a_recv p q lb t, l_msg l_recv q' K =>
           if q == q'
           then match lookup lb K with
                | Some (t', s) => if t == t' then Some s else None
                | None => None
                end
           else None
         | _, _ => None
         end
    else
      None.

  Fixpoint do_act (a : act) (e : PEnv) : option PEnv :=
    match e with
    | [::] => None
    | h :: t => if h.1 == subject a
                then
                  match act_lty a h with
                  | None => None
                  | Some L =>
                    if L == l_end then Some t
                    else Some ((h.1, L) :: t)
                  end
                else
                 match do_act a t with
                  | None => None
                  | Some t' => Some (h :: t')
                  end
    end.

  (** lstep a Q P Q' P' is the 'step' relation <Q, P> ->^a <Q', P'> in Coq*)
  Inductive lstep : act -> MsgQ * PEnv -> MsgQ * PEnv -> Prop :=
  | ls_send t p q lb P Q P' Q' :
      Q' == enqueue Q ((p, q), (lb, t)) ->
      Some P' == do_act (a_send p q lb t) P ->
      lstep (a_send p q lb t) (Q, P) (Q', P')
  | ls_recv t p q lb P Q P' Q' :
      Some ((lb, t), Q') == dequeue Q (p, q) ->
      Some P' == do_act (a_recv p q lb t) P ->
      lstep (a_recv p q lb t) (Q, P) (Q', P')
  .

  CoInductive l_lts : trace -> MsgQ * PEnv -> Prop :=
  | lt_end : l_lts tr_end ([::], [::])
  | lt_next a t P P' :
      lstep a P P' ->
      l_lts t P' ->
      l_lts (tr_next a t) P.

  Derive Inversion llts_inv with (forall tr G, l_lts tr G) Sort Prop.

End Semantics.
