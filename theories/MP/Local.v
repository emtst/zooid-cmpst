From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.MP.Atom.
Require Import MPST.MP.Role.
Require Import MPST.MP.Forall.
Require Import MPST.MP.LNVar.
Require Import MPST.MP.Actions.

Section Syntax.
  Inductive l_ty :=
  | l_end
  | l_var (v : rvar)
  | l_rec (L : l_ty)
  | l_send (r : role) (t : mty) (L : l_ty)
  | l_recv (r : role) (t : mty) (L : l_ty)
  | l_brn (r : role) (K : seq (lbl * l_ty))
  | l_sel (r : role) (K : seq (lbl * l_ty)).

  Notation lfv a := (l_var (Rvar.fv a)).
  Notation lbv n := (l_var (Rvar.bv n)).

  Lemma lty_ind :
    forall (P : l_ty -> Prop),
      P l_end ->
      (forall v, P (l_var v)) ->
      (forall G, P G -> P (l_rec G)) ->
      (forall r t G, P G -> P (l_send r t G)) ->
      (forall r t G, P G -> P (l_recv r t G)) ->
      (forall p K, Forall (fun lL => P lL.2) K -> P (l_brn p K)) ->
      (forall p K, Forall (fun lL => P lL.2) K -> P (l_sel p K)) ->
      forall l : l_ty, P l.
  Proof.
    move => P P_end P_var P_rec P_send P_recv P_brn P_sel.
    fix Ih 1; case=>[|v|L|r t L|r t L|r K|r K].
    + by apply: P_end.
    + by apply: P_var.
    + by apply: P_rec.
    + by apply: P_send.
    + by apply: P_recv.
    + by apply: P_brn; elim: K.
    + by apply: P_sel; elim: K.
  Qed.

  Fixpoint depth_lty L :=
    match L with
    | l_end
    | l_var _ => 0
    | l_rec L
    | l_recv _ _ L
    | l_send _ _ L => (depth_lty L).+1
    | l_sel _ K
    | l_brn _ K  => (maximum [seq depth_lty l.2 | l <- K]).+1
    end.

  Fixpoint eq_lty x y :=
    match x, y with
    | l_end, l_end => true
    | l_var x, l_var y => x == y
    | l_rec x, l_rec y => eq_lty x y
    | l_recv r1 t1 L1, l_recv r2 t2 L2
    | l_send r1 t1 L1, l_send r2 t2 L2
      => (r1 == r2) && (t1 == t2) && eq_lty L1 L2
    | l_sel r1 K1, l_sel r2 K2
    | l_brn r1 K1, l_brn r2 K2
      => (r1 == r2)
           && (fix eqK K1 K2 :=
                 match K1, K2 with
                 | [::], [::] => true
                 | (l1, L1)::K1, (l2, L2)::K2 =>
                   (l1 == l2) && eq_lty L1 L2 && eqK K1 K2
                 | _, _ => false
                 end) K1 K2
           (* all2 (fun l r => (l.1 == r.1) && eq_lty l.2 r.2) K1 K2 *)
    | _, _ => false
    end.

  Definition eq_lalt (l r : lbl * l_ty) := (l.1 == r.1) && eq_lty l.2 r.2.

  Lemma eqbrn_all r1 r2 K1 K2 :
    eq_lty (l_brn r1 K1) (l_brn r2 K2) = (r1 == r2) && all2 eq_lalt K1 K2.
  Proof.
    rewrite /=; case: eqP=>///= _; move: K1 K2 {r1 r2}.
    by elim=>//[[l1 L1] K1] Ih; case=>//[[l2 L2] K2]/=; rewrite Ih.
  Qed.

  Lemma eqsel_all r1 r2 K1 K2 :
    eq_lty (l_sel r1 K1) (l_sel r2 K2) = (r1 == r2) && all2 eq_lalt K1 K2.
  Proof.
    rewrite /=; case: eqP=>///= _; move: K1 K2 {r1 r2}.
    by elim=>//[[l1 L1] K1] Ih; case=>//[[l2 L2] K2]/=; rewrite Ih.
  Qed.

  Lemma lty_eqP : Equality.axiom eq_lty.
  Proof.
    rewrite /Equality.axiom; fix Ih 1 => x y.
    case: x => [|v|L|r t L|r t L|r K|r K];
       case: y =>[|v'|L'|r' t' L'|r' t' L'|r' K'|r' K']; try (by constructor).
    + by rewrite /eq_lty; case: eqP=>[->|F]; constructor=>//[[/F]].
    + by rewrite /=; case: Ih=>[->|F]; constructor=>//[[/F]].
    + rewrite /=; do 2 (case: eqP=>[->|F];[|constructor=>[[/F]]//]).
      by case: Ih=>[->|F];constructor=>//[[/F]].
    + rewrite /=; do 2 (case: eqP=>[->|F];[|constructor=>[[/F]]//]).
      by case: Ih=>[->|F];constructor=>//[[/F]].
    + rewrite eqbrn_all; case: eqP=>[<-|F];[|constructor=>[[/F]]//];move:K'=>/=.
      elim: K=>[|[l L] K IhK]; case=>[|[l' L']K']/=; try (by constructor).
      rewrite {1}/eq_lalt/=; case: eqP=>[<-|F];[|constructor=>[[/F]]//].
      case: Ih=>[<-|F];[|constructor=>[[/F]]//].
      by case: IhK=>[[]<-|F]; constructor=>//[[]]H; apply: F; rewrite H.
    + rewrite eqsel_all; case: eqP=>[<-|F];[|constructor=>[[/F]]//];move:K'=>/=.
      elim: K=>[|[l L] K IhK]; case=>[|[l' L']K']/=; try (by constructor).
      rewrite {1}/eq_lalt/=; case: eqP=>[<-|F];[|constructor=>[[/F]]//].
      case: Ih=>[<-|F];[|constructor=>[[/F]]//].
      by case: IhK=>[[]<-|F]; constructor=>//[[]]H; apply: F; rewrite H.
  Qed.

  Definition lty_eqMixin := EqMixin lty_eqP.
  Canonical lty_eqType := Eval hnf in EqType l_ty lty_eqMixin.

  Fixpoint l_open (d : nat) (L2 : l_ty) (L1 : l_ty) :=
    match L1 with
    | l_end => L1
    | l_var v => Rvar.open l_var d L2 v
    | l_rec L => l_rec (l_open d.+1 L2 L)
    | l_send p t L => l_send p t (l_open d L2 L)
    | l_recv p t L => l_recv p t (l_open d L2 L)
    | l_brn p K => l_brn p [seq (lL.1, l_open d L2 lL.2) | lL <- K]
    | l_sel p K => l_sel p [seq (lL.1, l_open d L2 lL.2) | lL <- K]
    end.
  Notation "{ k '~>' v } L":= (l_open k v L) (at level 30, right associativity).
  Notation "L '^' v":= (l_open 0 (lfv v) L) (at level 30, right associativity).

  Fixpoint l_close (v : atom) (d : nat) (L1 : l_ty) :=
    match L1 with
    | l_end => L1
    | l_var lv => l_var (Rvar.close v d lv)
    | l_rec L => l_rec (l_close v d.+1 L)
    | l_send p t L => l_send p t (l_close v d L)
    | l_recv p t L => l_recv p t (l_close v d L)
    | l_brn p K => l_brn p [seq (lL.1, l_close v d lL.2) | lL <- K]
    | l_sel p K => l_sel p [seq (lL.1, l_close v d lL.2) | lL <- K]
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

  Lemma lclose_brn_zip v d p K :
    l_close v d (l_brn p K)
    = l_brn p (zip (unzip1 K) [seq l_close v d x | x <- unzip2 K]).
  Proof. by rewrite /= unzip2_lift (unzip1_map2 (l_close v d)) zip_unzip. Qed.

  Lemma lclose_sel_zip v d p K :
    l_close v d (l_sel p K)
    = l_sel p (zip (unzip1 K) [seq l_close v d x | x <- unzip2 K]).
  Proof. by rewrite /= unzip2_lift (unzip1_map2 (l_close v d)) zip_unzip. Qed.

  Definition fsetUs (K : choiceType) : seq {fset K} -> {fset K}
    := foldl fsetU fset0.

  Lemma notin_unions (X : choiceType) (x : X) (l : seq {fset X}) :
    (x \notin fsetUs l) <-> Forall (fun e => x \notin e) l.
  Proof.
    rewrite /fsetUs Fa_rev -(revK l) foldl_rev revK; move: (rev l)=> {l}l.
    by elim: l => // a l Ih /=; rewrite fsetUC in_fsetU negb_or -(rwP andP) Ih.
  Qed.

  Fixpoint l_fvar (L : l_ty) : {fset atom} :=
    match L with
    | l_end => fset0
    | l_var v => Rvar.fvar v
    | l_rec L
    | l_recv _ _ L
    | l_send _ _ L => l_fvar L
    | l_sel _ K
    | l_brn _ K => fsetUs [seq l_fvar lL.2 | lL <- K]
    end.

  Fixpoint l_fbvar (d : nat) (L : l_ty) : {fset nat} :=
    match L with
    | l_end => fset0
    | l_var v => Rvar.fbvar d v
    | l_rec L => l_fbvar d.+1 L
    | l_recv _ _ L
    | l_send _ _ L => l_fbvar d L
    | l_sel _ K
    | l_brn _ K => fsetUs [seq l_fbvar d lL.2 | lL <- K]
    end.

  Lemma l_open_close X L n : X \notin l_fvar L -> {n <~ X}{n ~> lfv X}L = L.
  Proof.
    elim/lty_ind: L n=>[|v|L Ih|r t L Ih|r t L Ih|r K Ih|r K Ih] n /=Fv//;
      try (by rewrite Ih).
    + by move: Fv; rewrite Rvar.open_fun/= =>H; rewrite Rvar.open_close.
    + move: Ih=>/Fa_lift/(_ n)-Ih; move: Fv => /notin_unions/Fa_map-Fv.
      move: (Fa_app (Fa_conj Ih Fv)) => {Ih Fv}Ih; rewrite -map_comp /comp/=.
      by elim: K Ih=>// [[l L] K Ih/= [-> /Ih-[->]]].
    + move: Ih=>/Fa_lift/(_ n)-Ih; move: Fv => /notin_unions/Fa_map-Fv.
      move: (Fa_app (Fa_conj Ih Fv)) => {Ih Fv}Ih; rewrite -map_comp /comp/=.
      by elim: K Ih=>// [[l L] K Ih/= [-> /Ih-[->]]].
  Qed.

  Lemma l_close_open n X L : n \notin l_fbvar 0 L -> {n ~> lfv X}{n <~ X}L = L.
  Proof.
    move: {1 3}n (add0n n)=>n0; elim/lty_ind: L 0 n =>///=.
    - by move=>v n n1;rewrite addnC Rvar.open_fun=><-H;rewrite Rvar.close_open.
    - by move=>G Ih n n1 Eq/= H; rewrite (Ih n.+1 n1.+1) // -Eq.
    - by move=> r t G Ih n n1 Eq/= H; rewrite (Ih n n1).
    - by move=> r t G Ih n n1 Eq/= H; rewrite (Ih n n1).
    - move=> r K /Fa_lift-Ih n n1 Eq /notin_unions/Fa_map-H.
      move:Ih=>/(_ n)/Fa_lift/(_ n1)/Fa_lift/(_ Eq)/Fa_conj/( _ H)/Fa_app-Ih{H}.
      rewrite -map2_zip -unzip1_map2 unzip2_lift /unzip2 -!map_comp /comp/=.
      by rewrite (Fa_map_eq Ih) zip_unzip.
    - move=> r K /Fa_lift-Ih n n1 Eq /notin_unions/Fa_map-H.
      move:Ih=>/(_ n)/Fa_lift/(_ n1)/Fa_lift/(_ Eq)/Fa_conj/( _ H)/Fa_app-Ih{H}.
      rewrite -map2_zip -unzip1_map2 unzip2_lift /unzip2 -!map_comp /comp/=.
      by rewrite (Fa_map_eq Ih) zip_unzip.
  Qed.

  Lemma l_depth_open L X : depth_lty L = depth_lty (L^X).
  Proof.
    move: 0; elim/lty_ind: L=>/=//.
    + by move=>v n; rewrite Rvar.open_fun.
    + by move=> L Ih n; rewrite (Ih n.+1).
    + by move=> _ _ L Ih n; rewrite (Ih n).
    + by move=> _ _ L Ih n; rewrite (Ih n).
    + move=> _ K Ih n; rewrite -map_comp /comp/=.
      by move: Ih => /Fa_lift/(_ n)/Fa_map_eq<-.
    + move=> _ K Ih n; rewrite -map_comp /comp/=.
      by move: Ih => /Fa_lift/(_ n)/Fa_map_eq<-.
  Qed.

  Lemma lty_ind1 :
    forall (P : l_ty -> Prop),
      P l_end ->
      (forall v, P (l_var v)) ->
      (forall L, (forall X (s : {fset atom}), X \notin s -> P (L ^ X)) ->
                 P (l_rec L)) ->
      (forall r t L, P L -> P (l_send r t L)) ->
      (forall r t L, P L -> P (l_recv r t L)) ->
      (forall p K, (forall l L, (l, L) \in K -> P L) -> P (l_brn p K)) ->
      (forall p K, (forall l L, (l, L) \in K -> P L) -> P (l_sel p K)) ->
      forall l : l_ty, P l.
  Proof.
    move => P P_end P_var P_rec P_send P_recv P_brn P_sel L.
    move: {-1}(depth_lty L) (leqnn (depth_lty L))=> n; move: n L; elim.
    + by case.
    + move=>n Ih; case=>/=//.
      - by move=>L D; apply:P_rec=>X S _;apply: Ih;rewrite -(l_depth_open L X).
      - by move=> r t L D; apply: P_send; apply: Ih.
      - by move=> r t L D; apply: P_recv; apply: Ih.
      - move=> r K D;apply: P_brn=>l L /(map_f (fun X => depth_lty X.2)).
        move=>/in_maximum_leq-/=dG; move: (leq_trans dG D)=>{dG} {D}.
        by apply: Ih.
      - move=> r K D;apply: P_sel=>l L /(map_f (fun X => depth_lty X.2)).
        move=>/in_maximum_leq-/=dG; move: (leq_trans dG D)=>{dG} {D}.
        by apply: Ih.
  Qed.
End Syntax.

Section Session.

  Inductive s_ty :=
  | s_end
  | s_var (v : rvar)
  | s_rec (S : s_ty)
  | s_send (t : mty) (S : s_ty)
  | s_recv (t : mty) (L : s_ty)
  | s_brn (K : seq (lbl * s_ty))
  | s_sel (K : seq (lbl * s_ty)).

  Fixpoint eq_sty x y :=
    match x, y with
    | s_end, s_end => true
    | s_var x, s_var y => x == y
    | s_rec x, s_rec y => eq_sty x y
    | s_recv t1 S1, s_recv t2 S2
    | s_send t1 S1, s_send t2 S2
      => (t1 == t2) && eq_sty S1 S2
    | s_sel K1, s_sel K2
    | s_brn K1, s_brn K2
      => (fix eqK K1 K2 :=
            match K1, K2 with
            | [::], [::] => true
            | (l1, S1)::K1, (l2, S2)::K2 =>
              (l1 == l2) && eq_sty S1 S2 && eqK K1 K2
            | _, _ => false
            end) K1 K2
           (* all2 (fun l r => (l.1 == r.1) && eq_lty l.2 r.2) K1 K2 *)
    | _, _ => false
    end.

  Definition eq_salt (l r : lbl * s_ty) := (l.1 == r.1) && eq_sty l.2 r.2.

  Lemma eq_sbrn_all K1 K2 :
    eq_sty (s_brn K1) (s_brn K2) = all2 eq_salt K1 K2.
  Proof.
    rewrite /=; move: K1 K2.
    by elim=>//[[l1 L1] K1] Ih; case=>//[[l2 L2] K2]/=; rewrite Ih.
  Qed.

  Lemma eq_ssel_all K1 K2 :
    eq_sty (s_sel K1) (s_sel K2) = all2 eq_salt K1 K2.
  Proof.
    rewrite /=; move: K1 K2.
    by elim=>//[[l1 L1] K1] Ih; case=>//[[l2 L2] K2]/=; rewrite Ih.
  Qed.

  Lemma sty_eqP : Equality.axiom eq_sty.
  Proof.
    rewrite /Equality.axiom; fix Ih 1 => x y.
    case: x => [|v|L|t L|t L|K|K];
       case: y =>[|v'|L'|t' L'|t' L'|K'|K']; try (by constructor).
    + by rewrite /eq_sty; case: eqP=>[->|F]; constructor=>//[[/F]].
    + by rewrite /=; case: Ih=>[->|F]; constructor=>//[[/F]].
    + rewrite /=; case: eqP=>[->|F];[|constructor=>[[/F]]//].
      by case: Ih=>[->|F];constructor=>//[[/F]].
    + rewrite /=; case: eqP=>[->|F];[|constructor=>[[/F]]//].
      by case: Ih=>[->|F];constructor=>//[[/F]].
    + rewrite eq_sbrn_all; move: K'.
      elim: K=>[|[l L] K IhK]; case=>[|[l' L']K']/=; try (by constructor).
      rewrite {1}/eq_salt/=; case: eqP=>[<-|F];[|constructor=>[[/F]]//].
      case: Ih=>[<-|F];[|constructor=>[[/F]]//].
      by case: IhK=>[[]<-|F]; constructor=>//[[]]H; apply: F; rewrite H.
    + rewrite eq_ssel_all; move:K'=>/=.
      elim: K=>[|[l L] K IhK]; case=>[|[l' L']K']/=; try (by constructor).
      rewrite {1}/eq_salt/=; case: eqP=>[<-|F];[|constructor=>[[/F]]//].
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
    | s_send t s => s_send t (s_open d S2 s)
    | s_recv t s => s_recv t (s_open d S2 s)
    | s_brn K => s_brn [seq (lS.1, s_open d S2 lS.2) | lS <- K]
    | s_sel K => s_sel [seq (lS.1, s_open d S2 lS.2) | lS <- K]
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
    | s_send t L => s_send t (s_close v d L)
    | s_recv t L => s_recv t (s_close v d L)
    | s_brn K => s_brn [seq (lL.1, s_close v d lL.2) | lL <- K]
    | s_sel K => s_sel [seq (lL.1, s_close v d lL.2) | lL <- K]
    end.
  Notation "{ k '<~' v } L":= (s_close v k L) (at level 30, right associativity).

  Fixpoint s_fvar (L : s_ty) : {fset atom} :=
    match L with
    | s_end => fset0
    | s_var v => Rvar.fvar v
    | s_rec L
    | s_recv _ L
    | s_send _ L => s_fvar L
    | s_sel K
    | s_brn K => fsetUs [seq s_fvar lL.2 | lL <- K]
    end.

  Fixpoint s_fbvar (d : nat) (L : s_ty) : {fset nat} :=
    match L with
    | s_end => fset0
    | s_var v => Rvar.fbvar d v
    | s_rec L => s_fbvar d.+1 L
    | s_recv _ L
    | s_send _ L => s_fbvar d L
    | s_sel K
    | s_brn K => fsetUs [seq s_fbvar d lL.2 | lL <- K]
    end.

  Lemma sty_ind :
    forall (P : s_ty -> Prop),
      P s_end ->
      (forall v, P (s_var v)) ->
      (forall s, P s -> P (s_rec s)) ->
      (forall t s, P s -> P (s_send t s)) ->
      (forall t s, P s -> P (s_recv t s)) ->
      (forall K, Forall (fun lS => P lS.2) K -> P (s_brn K)) ->
      (forall K, Forall (fun lS => P lS.2) K -> P (s_sel K)) ->
      forall s : s_ty, P s.
  Proof.
    move => P P_end P_var P_rec P_send P_recv P_brn P_sel.
    fix Ih 1; case=>[|v|L|t L|t L|K|K].
    + by apply: P_end.
    + by apply: P_var.
    + by apply: P_rec.
    + by apply: P_send.
    + by apply: P_recv.
    + by apply: P_brn; elim: K.
    + by apply: P_sel; elim: K.
  Qed.

  Lemma s_open_close X L n : X \notin s_fvar L -> {n <~ X}{n ~> sfv X}L = L.
  Proof.
    elim/sty_ind: L n=>[|v|L Ih|t L Ih|t L Ih|K Ih|K Ih] n /=Fv//;
      try (by rewrite Ih).
    + by move: Fv; rewrite Rvar.open_fun/= =>H; rewrite Rvar.open_close.
    + move: Ih=>/Fa_lift/(_ n)-Ih; move: Fv => /notin_unions/Fa_map-Fv.
      move: (Fa_app (Fa_conj Ih Fv)) => {Ih Fv}Ih; rewrite -map_comp /comp/=.
      by elim: K Ih=>// [[l L] K Ih/= [-> /Ih-[->]]].
    + move: Ih=>/Fa_lift/(_ n)-Ih; move: Fv => /notin_unions/Fa_map-Fv.
      move: (Fa_app (Fa_conj Ih Fv)) => {Ih Fv}Ih; rewrite -map_comp /comp/=.
      by elim: K Ih=>// [[l L] K Ih/= [-> /Ih-[->]]].
  Qed.

  Lemma s_close_open n X L : n \notin s_fbvar 0 L -> {n ~> sfv X}{n <~ X}L = L.
  Proof.
    move: {1 3}n (add0n n)=>n0; elim/sty_ind: L 0 n =>///=.
    - by move=>v n n1;rewrite addnC Rvar.open_fun=><-H;rewrite Rvar.close_open.
    - by move=>G Ih n n1 Eq/= H; rewrite (Ih n.+1 n1.+1) // -Eq.
    - by move=> t G Ih n n1 Eq/= H; rewrite (Ih n n1).
    - by move=> t G Ih n n1 Eq/= H; rewrite (Ih n n1).
    - move=> K /Fa_lift-Ih n n1 Eq /notin_unions/Fa_map-H.
      move:Ih=>/(_ n)/Fa_lift/(_ n1)/Fa_lift/(_ Eq)/Fa_conj/( _ H)/Fa_app-Ih{H}.
      rewrite -map2_zip -unzip1_map2 unzip2_lift /unzip2 -!map_comp /comp/=.
      by rewrite (Fa_map_eq Ih) zip_unzip.
    - move=> K /Fa_lift-Ih n n1 Eq /notin_unions/Fa_map-H.
      move:Ih=>/(_ n)/Fa_lift/(_ n1)/Fa_lift/(_ Eq)/Fa_conj/( _ H)/Fa_app-Ih{H}.
      rewrite -map2_zip -unzip1_map2 unzip2_lift /unzip2 -!map_comp /comp/=.
      by rewrite (Fa_map_eq Ih) zip_unzip.
  Qed.

  Fixpoint depth_sty L :=
    match L with
    | s_end
    | s_var _ => 0
    | s_rec L
    | s_recv _ L
    | s_send _ L => (depth_sty L).+1
    | s_sel K
    | s_brn K  => (maximum [seq depth_sty l.2 | l <- K]).+1
    end.

  Lemma s_depth_open L X : depth_sty L = depth_sty (L^X).
  Proof.
    move: 0; elim/sty_ind: L=>/=//.
    + by move=>v n; rewrite Rvar.open_fun.
    + by move=> L Ih n; rewrite (Ih n.+1).
    + by move=> _ L Ih n; rewrite (Ih n).
    + by move=> _ L Ih n; rewrite (Ih n).
    + move=> K Ih n; rewrite -map_comp /comp/=.
      by move: Ih => /Fa_lift/(_ n)/Fa_map_eq<-.
    + move=> K Ih n; rewrite -map_comp /comp/=.
      by move: Ih => /Fa_lift/(_ n)/Fa_map_eq<-.
  Qed.

  Lemma sty_ind1 :
    forall (P : s_ty -> Prop),
      P s_end ->
      (forall v, P (s_var v)) ->
      (forall s, (forall X (A : {fset atom}), X \notin A -> P (s ^ X)) ->
                 P (s_rec s)) ->
      (forall t s, P s -> P (s_send t s)) ->
      (forall t s, P s -> P (s_recv t s)) ->
      (forall K, (forall l s, (l, s) \in K -> P s) -> P (s_brn K)) ->
      (forall K, (forall l s, (l, s) \in K -> P s) -> P (s_sel K)) ->
      forall s : s_ty, P s.
  Proof.
    move => P P_end P_var P_rec P_send P_recv P_brn P_sel L.
    move: {-1}(depth_sty L) (leqnn (depth_sty L))=> n; move: n L; elim.
    + by case.
    + move=>n Ih; case=>/=//.
      - by move=>L D; apply:P_rec=>X S _;apply: Ih;rewrite -(s_depth_open L X).
      - by move=> t L D; apply: P_send; apply: Ih.
      - by move=> t L D; apply: P_recv; apply: Ih.
      - move=> K D;apply: P_brn=>l L /(map_f (fun X => depth_sty X.2)).
        move=>/in_maximum_leq-/=dG; move: (leq_trans dG D)=>{dG} {D}.
        by apply: Ih.
      - move=> K D;apply: P_sel=>l L /(map_f (fun X => depth_sty X.2)).
        move=>/in_maximum_leq-/=dG; move: (leq_trans dG D)=>{dG} {D}.
        by apply: Ih.
  Qed.

  Definition pmerge (s : option s_ty) (l : lbl * s_ty) :=
    match s, l with
    | None, _ => None
    | Some s, (_, s') => if s == s' then Some s else None
    end.

  Definition partial_merge (l : seq (lbl * s_ty)) :=
    match l with
    | [::] => None
    | h :: t => foldl pmerge (Some h.2) t
    end.

  Definition ms_send t L :=
    match L with
    | Some L => Some (s_send t L)
    | None => None
    end.

  Definition ms_recv t L :=
    match L with
    | Some L => Some (s_recv t L)
    | None => None
    end.

  Fixpoint merge (A: eqType) (oL : A) (K : seq (lbl * option A)) :=
    match K with
    | [::] => Some oL
    | h::t => if h.2 == Some oL then merge oL t
              else None
    end.

  Definition merge_all (A : eqType) (K : seq (lbl * option A)) :=
    match K with
    | [::] => None
    | (h :: t) =>
      match h.2 with
      | Some o => merge o t
      | None => None
      end
    end.

  Fixpoint flatten A (L : seq (lbl * option A)) :=
    match L with
    | [::] => Some [::]
    | h :: t => match h.2, flatten t with
                | None, _ => None
                | _, None => None
                | Some s, Some t => Some ((h.1, s) :: t)
                end
    end.

  Definition flat_alts A (L : seq (lbl * option A)) :=
    match L with
    | [::] => None
    | _ => flatten L
    end.

  Definition ms_sel L :=
    match flat_alts L with
    | Some L => Some (s_sel L)
    | None => None
    end.

  Definition ms_brn L :=
    match flat_alts L with
    | Some L => Some (s_brn L)
    | None => None
    end.

  Definition ms_rec s :=
    match s with
    | None => None
    | Some s => Some (s_rec s)
    end.

  Fixpoint partial_proj (l : l_ty) (r : role) : option s_ty :=
    match l with
    | l_end => Some (s_end)
    | l_var v => Some (s_var v)
    | l_rec L =>
      let: s := partial_proj L r in
      if s == Some (sbv 0) then Some s_end else ms_rec s
    | l_recv p t L =>
      if p == r then ms_recv t (partial_proj L r) else partial_proj L r
    | l_send p t L =>
      if p == r then ms_send t (partial_proj L r) else partial_proj L r
    | l_sel p K =>
      if p == r then ms_sel [seq (X.1, partial_proj X.2 r) | X <- K]
      else merge_all [seq (X.1, partial_proj X.2 r) | X <- K]
    | l_brn p K  =>
      if p == r then ms_brn [seq (X.1, partial_proj X.2 r) | X <- K]
      else merge_all [seq (X.1, partial_proj X.2 r) | X <- K]
    end.

  Fixpoint dual (L : s_ty) : s_ty :=
    match L with
    | s_end => s_end
    | s_var v => s_var v
    | s_rec s => s_rec (dual s)
    | s_send t L =>  s_recv t (dual L)
    | s_recv t L =>  s_send t (dual L)
    | s_brn K => s_sel [seq (x.1, dual x.2) | x <- K]
    | s_sel K => s_brn [seq (x.1, dual x.2) | x <- K]
    end.

  Lemma dualK s : dual (dual s) = s.
  Proof.
    elim/sty_ind: s=>[|v|s Ih|t s Ih| t s Ih|K Ih|K Ih]//; try (by rewrite /=Ih).
    - rewrite /= -map_comp /comp/=.
      by elim: K Ih=>[//|[l s] K Ihl /= [-> /Ihl-[->]]].
    - rewrite /= -map_comp /comp/=.
      by elim: K Ih=>[//|[l s] K Ihl /= [-> /Ihl-[->]]].
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
End Session.

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
         | a_send p, l_send q ty L' =>
           if (p.1.2 == q) && (p.2 == ty) then Some L'
           else None
         | a_recv p, l_recv q ty L' =>
           if (p.1.1 == q) && (p.2 == ty) then Some L'
           else None
         | a_brn p q lb, l_brn q' K =>
           if q == q'
           then lookup lb K
           else None
         | a_sel p q lb, l_sel p' K =>
           if p == p'
           then lookup lb K
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

  Definition enqueue_msg (Q : MsgQ) p := enqueue Q (p.1, inr p.2) .
  Definition enqueue_lbl (Q : MsgQ) p q lb := enqueue Q ((p, q), inl lb) .
  (** lstep a Q P Q' P' is the 'step' relation <Q, P> ->^a <Q', P'> in Coq*)
  Inductive lstep : act -> MsgQ * PEnv -> MsgQ * PEnv -> Prop :=
  | ls_snd p P Q P' Q' :
      Q' == enqueue_msg Q p ->
      Some P' == do_act (a_send p) P ->
      lstep (a_send p) (Q, P) (Q', P')
  | ls_rcv p P Q P' Q' :
      Some (inr p.2, Q') == dequeue Q p.1 ->
      Some P' == do_act (a_recv p) P ->
      lstep (a_recv p) (Q, P) (Q', P')
  | ls_sel p q lb P Q P' Q' :
      Q' == enqueue_lbl Q p q lb ->
      Some P' == do_act (a_sel p q lb) P ->
      lstep (a_sel p q lb) (Q, P) (Q', P')
  | ls_brn p q lb P Q P' Q' :
      Some (inl lb, Q') == dequeue Q (p, q) ->
      Some P' == do_act (a_sel p q lb) P ->
      lstep (a_brn p q lb) (Q, P) (Q', P')
  .

  CoInductive l_lts : trace -> MsgQ * PEnv -> Prop :=
  | lt_end : l_lts tr_end ([::], [::])
  | lt_next a t P P' :
      lstep a P P' ->
      l_lts t P' ->
      l_lts (tr_next a t) P.

  Derive Inversion llts_inv with (forall tr G, l_lts tr G) Sort Prop.

End Semantics.
