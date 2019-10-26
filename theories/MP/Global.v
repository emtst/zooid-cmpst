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

  Inductive g_ty :=
  | g_end
  | g_var (v : rvar)
  | g_rec (G : g_ty)
  | g_msg (p : g_prefix) (G : g_ty)
  | g_brn (p : g_prefix) (K : seq (lbl * g_ty)).

  Notation gfv a := (g_var (Rvar.fv a)).
  Notation gbv n := (g_var (Rvar.bv n)).

  Fixpoint depth_gty a :=
    match a with
    | g_end
    | g_var _ => 0
    | g_rec G
    | g_msg _ G => (depth_gty G).+1
    | g_brn p K => (maximum (map (fun x=> depth_gty x.2) K)).+1
    end.

  Fixpoint participants G :=
    match G with
    | g_end
    | g_var _ => [::]
    | g_rec G => participants G
    | g_msg ((p, q), _) G => p::q::participants G
    | g_brn ((p, q), _) K => p::q::flatten [seq participants x.2 | x <- K]
    end.

  Lemma gty_ind1 :
    forall (P : g_ty -> Prop),
      P g_end ->
      (forall v, P (g_var v)) ->
      (forall G, P G -> P (g_rec G)) ->
      (forall p G, P G -> P (g_msg p G)) ->
      (forall p Gs, (forall lG, member lG Gs -> P lG.2) -> P (g_brn p Gs)) ->
      forall g : g_ty, P g.
  Proof.
    move=> P P_end P_var P_rec P_msg P_branch; fix Ih 1; case.
    + by apply: P_end.
    + by apply: P_var.
    + by move=>G; apply: P_rec=>//.
    + by move=>p G; apply: P_msg=>//.
    + move=>p Gs; apply: P_branch; apply/forall_member; elim Gs.
      - by [].
      - move=> lG1 {Gs}Gs IhGs/=; split; first by apply Ih.
        apply: IhGs.
  Qed.

  Fixpoint eq_g_ty a b :=
    match a, b with
    | g_end, g_end => true
    | g_var v1, g_var v2 => v1 == v2
    | g_rec G1, g_rec G2 => eq_g_ty G1 G2
    | g_msg p1 G1, g_msg p2 G2 => (p1 == p2) && eq_g_ty G1 G2
    | g_brn p1 K1, g_brn p2 K2 =>
      (p1 == p2)
        && (fix eqL K1 K2 :=
              match K1, K2 with
              | [::], [::] => true
              | l::K1, r::K2 => (l.1 == r.1) && eq_g_ty l.2 r.2 && eqL K1 K2
              | _, _ => false
              end) K1 K2
    | _, _ => false
    end.

  Definition eq_alt (l r : lbl * g_ty) := (l.1 == r.1) && eq_g_ty l.2 r.2.

  Lemma eqgty_all p1 K1 p2 K2 :
    eq_g_ty (g_brn p1 K1) (g_brn p2 K2) =
    (p1 == p2) && all2 eq_alt K1 K2.
  Proof.
    rewrite /=; case: eqP=>///= _ {p1 p2}.
    by move: K2; elim: K1=>[|lG1 K1 Ih]; case=>[|lG2 K2]/=//; rewrite Ih.
  Qed.

  Lemma g_ty_eqP : Equality.axiom eq_g_ty.
  Proof.
    rewrite /Equality.axiom; fix Ih 1 => x y.
    case x =>[|vl| Gl |pl Gl| pl Gsl]; case y =>[|vr| Gr |pr Gr| pr Gsr];
      try (by constructor).
    + by rewrite /eq_g_ty; case: eqP=>[->|H];constructor=>//[[]].
    + by rewrite /=; case: Ih=>[->|H];constructor=>//[[]].
    + by rewrite /=; case:eqP=>[->|H]; case: Ih=>[->|H'];constructor=>//[[]].
    + rewrite eqgty_all; case: eqP=>[<-|H];[|constructor=>[[]]//] =>/=.
      elim: Gsl Gsr.
      - by case; constructor.
      - move=>[ll Gl] Gsl Ih' [|[lr Gr] Gsr] /=; try (by constructor).
        rewrite /eq_alt/=; case: eqP=>[->|F];[|constructor=>[[/F]]//].
        case: Ih=>[<-|F];[|constructor=>[[/F]]//].
        by case: Ih'=>[[]<-|F];constructor=>//[[F']]; move: F' F=>->.
  Qed.

  Definition g_ty_eqMixin := EqMixin g_ty_eqP.
  Canonical g_ty_eqType := Eval hnf in EqType g_ty g_ty_eqMixin.

  Lemma alt_eqP : Equality.axiom eq_alt.
  Proof.
    rewrite /Equality.axiom/eq_alt; move=>[l1 G1] [l2 G2]/=.
    case: eqP=>[<-|H]; last (by apply: ReflectF => [[/H]]).
    by case: g_ty_eqP=>[<-|H]; last (by apply: ReflectF =>[[/H]]); apply: ReflectT.
  Qed.

  Lemma gty_ind2 :
    forall (P : g_ty -> Prop),
      P g_end ->
      (forall v, P (g_var v)) ->
      (forall G, P G -> P (g_rec G)) ->
      (forall p G, P G -> P (g_msg p G)) ->
      (forall p Gs, Forall (fun lG => P lG.2) Gs -> P (g_brn p Gs)) ->
      forall g : g_ty, P g.
  Proof.
    move=> P P_end P_var P_rec P_msg P_branch; elim/gty_ind1=>//.
    by move=> p Gs /forall_member; apply: P_branch.
  Qed.

  Fixpoint g_open (d : nat) (G2 : g_ty) (G1 : g_ty) :=
    match G1 with
    | g_end => G1
    | g_var v => Rvar.open g_var d G2 v
    | g_rec G => g_rec (g_open d.+1 G2 G)
    | g_msg p G => g_msg p (g_open d G2 G)
    | g_brn p Gs => g_brn p [seq (lG.1, g_open d G2 lG.2) | lG <- Gs]
    end.
  Notation "{ k '~>' v } G":= (g_open k v G) (at level 30, right associativity).
  Notation "G '^' v":= (g_open 0 (gfv v) G) (at level 30, right associativity).

  Fixpoint g_close (v : atom) (d : nat) (G1 : g_ty) :=
    match G1 with
    | g_end => G1
    | g_var gv => g_var (Rvar.close v d gv)
    | g_rec G => g_rec (g_close v d.+1 G)
    | g_msg p G => g_msg p (g_close v d G)
    | g_brn p Gs => g_brn p [seq (lG.1, g_close v d lG.2) | lG <- Gs]
    end.
  Notation "{ k '<~' v } G":= (g_close v k G) (at level 30, right associativity).

  Definition fsetUs (K : choiceType) : seq {fset K} -> {fset K}
    := foldl fsetU fset0.

  Open Scope fset_scope.
  Fixpoint g_fvar (G : g_ty) : {fset atom} :=
    match G with
    | g_var v => Rvar.fvar v
    | g_rec G
    | g_msg _ G => g_fvar G
    | g_brn _ Gs => fsetUs [seq g_fvar lG.2 | lG <- Gs]
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
    | g_var v => Rvar.fbvar d v
    | g_rec G => g_fbvar d.+1 G
    | g_msg _ G => g_fbvar d G
    | g_brn _ Gs => fsetUs [seq g_fbvar d lG.2 | lG <- Gs]
    | g_end => fset0
    end.

  Definition g_lc (G : g_ty) := g_fbvar 0 G = fset0.

  Lemma in_gfvar_gfv (a a' : atom) : (a \in g_fvar (gfv a')) = (a == a').
  Proof.
    rewrite /g_fvar; case: fset1P=>[->|].
    - by rewrite eq_refl.
    - by move=> /eqP/negPf->.
  Qed.

  Lemma gopen_gfv n X (a : atom) : {n ~> X} gfv a = gfv a.
  Proof. by []. Qed.

  Lemma gclose_gfv n X (a : atom) :
    {n <~ X} gfv a = if X == a then (gbv n) else (gfv a).
  Proof. by rewrite /g_close/Rvar.close (fun_if g_var). Qed.

  Lemma g_open_close X G n : X \notin g_fvar G -> {n <~ X}{n ~> gfv X}G = G.
  Proof.
    elim/gty_ind2: G n =>//.
    - by move=> v d /= H; rewrite Rvar.open_fun /= (Rvar.open_close d H).
    - move=> G Ih d; rewrite /g_fvar -/(g_fvar _)=>/Ih-{Ih}Ih.
      by rewrite -[in RHS](Ih d.+1).
    - move=> p G Ih d; rewrite /g_fvar -/(g_fvar _)=>/Ih-{Ih}Ih.
      by rewrite -[in RHS](Ih d).
    - move=> p Gs /Fa_lift-Ih n; move: (Ih n)=>{Ih}Ih.
      rewrite notin_fold_all -/g_fvar all_map /preim/=.
      rewrite /SimplPred/= -map_comp/comp/= =>/forallbP/=.
      move=>/(Fa_conj Ih)/Fa_app{Ih}/Fa_map_eq-Ih; congr g_brn.
      by elim: Gs Ih=>[//|[l G] Gs /= Ih [->/Ih->]].
  Qed.

  Lemma g_close_open n X G : n \notin g_fbvar 0 G -> {n ~> gfv X}{n <~ X}G = G.
  Proof.
    move: {1 3}n (add0n n)=>n0; elim/gty_ind2: G 0 n =>///=.
    - by move=> v n n1 <- H; rewrite addnC Rvar.open_fun Rvar.close_open.
    - move=> G Ih d n Eq n_in; congr g_rec; apply: (Ih d.+1)=>//.
      by rewrite -Eq.
    - by move=> p G Ih d n Eq n_in; congr g_msg; apply: (Ih d).
    - move=> p Gs /Fa_lift-Fa d n Eq; rewrite notin_fold_all !all_map /preim/=.
      move: (Fa d)=>{Fa}/Fa_lift/(_ n)/Fa_lift/(_ Eq)-Fa.
      move=>/forallbP/(Fa_conj Fa){Fa}.
      rewrite /SimplPred/= =>/Fa_app/Fa_map_eq-Ih.
      rewrite -map_comp /comp/=; congr g_brn => {Eq} {d} {n0} {p}.
      by elim: Gs Ih=>[//|/=[l G] Gs Ih [-> /Ih->]].
  Qed.
  Close Scope fset_scope.

  Lemma g_depth_open G X : depth_gty G = depth_gty (G^X).
  Proof.
    move: 0; elim/gty_ind2: G=>/=//.
    + by move=>v n; rewrite Rvar.open_fun.
    + by move=> G Ih n; rewrite (Ih n.+1).
    + by move=> _ G Ih n; rewrite (Ih n).
    + move=> _ Gs /Fa_lift-Ih n; move: (Ih n) => {Ih}/Fa_map_eq.
      rewrite -map_comp /comp/=.
      by elim: Gs=>[//|/=[l G] Gs Ih []<- /Ih-{Ih}[<-]].
  Qed.

  (* Induction scheme that takes into account that g_rec must be opened *)
  Lemma gty_ind3 :
    forall (P : g_ty -> Type),
      P g_end ->
      (forall v, P (g_var v)) ->
      (forall G, (forall X (s : {fset atom}), X \notin s -> P (G ^ X)) ->
                 P (g_rec G)) ->
      (forall p G, P G -> P (g_msg p G)) ->
      (forall p Gs, (forall l G, (l, G) \in Gs -> P G) -> P (g_brn p Gs)) ->
      forall g : g_ty, P g.
  Proof.
    move=> P P_end P_var P_rec P_msg P_brn G.
    move: {-1}(depth_gty G) (leqnn (depth_gty G))=> n; move: n G; elim.
    + by case.
    + move=>n Ih; case=>///=.
      - by move=> G dG; apply: P_rec => X S _; apply: Ih; rewrite -g_depth_open.
      - by move=> p G dG; apply: P_msg; apply: Ih.
      - move=> p Gs dGs; apply: P_brn => l G /(map_f (fun X => depth_gty X.2))/=.
        move=>/in_maximum_leq-dG; move: (leq_trans dG dGs)=>{dG} {dGs}.
        by apply: Ih.
  Qed.
End Syntax.

Section Semantics.

  (* Represents intermediate states in the execution *)
  Inductive rg_ty :=
  | rg_end
  | rg_var (v : rvar)
  | rg_rec (G : rg_ty)
  | rg_msg (p : g_prefix) (G : rg_ty)
  | rg_rcv (p : g_prefix) (G : rg_ty)
  | rg_brn (p : g_prefix) (K : seq (lbl * rg_ty))
  | rg_alt (l : lbl) (p : g_prefix) (G : rg_ty).


  Fixpoint init G :=
    match G with
    | g_end => rg_end
    | g_var v => rg_var v
    | g_rec G => rg_rec (init G)
    | g_msg p G => rg_msg p (init G)
    | g_brn p K => rg_brn p [seq (X.1, init X.2) | X <- K]
    end.

  Fixpoint eq_rg_ty a b :=
    match a, b with
    | rg_end, rg_end => true
    | rg_var v1, rg_var v2 => v1 == v2
    | rg_rec G1, rg_rec G2 => eq_rg_ty G1 G2
    | rg_msg p1 G1, rg_msg p2 G2 => (p1 == p2) && eq_rg_ty G1 G2
    | rg_rcv p1 G1, rg_rcv p2 G2 => (p1 == p2) && eq_rg_ty G1 G2
    | rg_alt lb1 p1 G1, rg_alt lb2 p2 G2
      => (lb1 == lb2) && (p1 == p2) && eq_rg_ty G1 G2
    | rg_brn p1 K1, rg_brn p2 K2 =>
      (p1 == p2)
        && (fix eqL K1 K2 :=
              match K1, K2 with
              | [::], [::] => true
              | l::K1, r::K2 => (l.1 == r.1) && eq_rg_ty l.2 r.2 && eqL K1 K2
              | _, _ => false
              end) K1 K2
    | _, _ => false
    end.

  Definition eq_rg_alt (l r : lbl * rg_ty) := (l.1 == r.1) && eq_rg_ty l.2 r.2.

  Lemma eqrgty_all p1 K1 p2 K2 :
    eq_rg_ty (rg_brn p1 K1) (rg_brn p2 K2) =
    (p1 == p2) && all2 eq_rg_alt K1 K2.
  Proof.
    rewrite /=; case: eqP=>///= _ {p1 p2}.
    by move: K2; elim: K1=>[|lG1 K1 Ih]; case=>[|lG2 K2]/=//; rewrite Ih.
  Qed.

  Lemma rg_ty_eqP : Equality.axiom eq_rg_ty.
  Proof.
    rewrite /Equality.axiom; fix Ih 1 => x y.
    case: x =>[|vl| Gl |pl Gl|pl Gl|pl Gsl|lb_l pl Gl];
               case: y =>[|vr| Gr |pr Gr|pr Gr|pr Gsr|lb_r pr Gr];
                          try (by constructor).
    + by rewrite /eq_rg_ty; case: eqP=>[->|H];constructor=>//[[]].
    + by rewrite /=; case: Ih=>[->|H];constructor=>//[[]].
    + by rewrite /=; case:eqP=>[->|H]; case: Ih=>[->|H'];constructor=>//[[]].
    + by rewrite /=; case:eqP=>[->|H]; case: Ih=>[->|H'];constructor=>//[[]].
    + rewrite eqrgty_all; case: eqP=>[<-|H];[|constructor=>[[]]//] =>/=.
      elim: Gsl Gsr.
      - by case; constructor.
      - move=>[ll Gl] Gsl Ih' [|[lr Gr] Gsr] /=; try (by constructor).
        rewrite /eq_rg_alt/=; case: eqP=>[->|F];[|constructor=>[[/F]]//].
        case: Ih=>[<-|F];[|constructor=>[[/F]]//].
        by case: Ih'=>[[]<-|F];constructor=>//[[F']]; move: F' F=>->.
    + by rewrite /=; case:eqP=>[->|H]; case:eqP=>[->|H'];
                     case: Ih=>[->|H''];constructor=>//[[]].
  Qed.

  Definition rg_ty_eqMixin := EqMixin rg_ty_eqP.
  Canonical rg_ty_eqType := Eval hnf in EqType rg_ty rg_ty_eqMixin.

  Lemma rgalt_eqP : Equality.axiom eq_rg_alt.
  Proof.
    rewrite /Equality.axiom/eq_rg_alt; move=>[l1 G1] [l2 G2]/=.
    case: eqP=>[<-|H]; last (by apply: ReflectF => [[/H]]).
    by case: rg_ty_eqP=>[<-|H]; last (by apply: ReflectF =>[[/H]]); apply: ReflectT.
  Qed.

  Lemma rgty_ind1 :
    forall (P : rg_ty -> Prop),
      P rg_end ->
      (forall v, P (rg_var v)) ->
      (forall G, P G -> P (rg_rec G)) ->
      (forall p G, P G -> P (rg_msg p G)) ->
      (forall p G, P G -> P (rg_rcv p G)) ->
      (forall lb p G, P G -> P (rg_alt lb p G)) ->
      (forall p Gs, (forall lG, member lG Gs -> P lG.2) -> P (rg_brn p Gs)) ->
      forall g : rg_ty, P g.
  Proof.
    move=> P P_end P_var P_rec P_msg P_rcv P_alt P_branch; fix Ih 1; case.
    + by apply: P_end.
    + by apply: P_var.
    + by move=>G; apply: P_rec=>//.
    + by move=>p G; apply: P_msg=>//.
    + by move=>p G; apply: P_rcv=>//.
    + move=>p Gs; apply: P_branch; apply/forall_member; elim Gs.
      - by [].
      - move=> lG1 {Gs}Gs IhGs/=; split; first by apply Ih.
        apply: IhGs.
    + by move=> lb p G; apply: P_alt =>//.
  Qed.

  Lemma rgty_ind2 :
    forall (P : rg_ty -> Prop),
      P rg_end ->
      (forall v, P (rg_var v)) ->
      (forall G, P G -> P (rg_rec G)) ->
      (forall p G, P G -> P (rg_msg p G)) ->
      (forall p G, P G -> P (rg_rcv p G)) ->
      (forall lb p G, P G -> P (rg_alt lb p G)) ->
      (forall p Gs, Forall (fun lG => P lG.2) Gs -> P (rg_brn p Gs)) ->
      forall g : rg_ty, P g.
  Proof.
    move=> P P_end P_var P_rec P_msg P_rcv P_alt P_branch; elim/rgty_ind1=>//.
    by move=> p Gs /forall_member; apply: P_branch.
  Qed.

  Fixpoint rg_open (d : nat) (G2 : rg_ty) (G1 : rg_ty) :=
    match G1 with
    | rg_end => G1
    | rg_var v => Rvar.open rg_var d G2 v
    | rg_rec G => rg_rec (rg_open d.+1 G2 G)
    | rg_msg p G => rg_msg p (rg_open d G2 G)
    | rg_rcv p G => rg_rcv p (rg_open d G2 G)
    | rg_brn p Gs => rg_brn p [seq (lG.1, rg_open d G2 lG.2) | lG <- Gs]
    | rg_alt l p G => rg_alt l p (rg_open d G2 G)
    end.

  Fixpoint rg_close (v : atom) (d : nat) (G1 : rg_ty) :=
    match G1 with
    | rg_end => G1
    | rg_var gv => rg_var (Rvar.close v d gv)
    | rg_rec G => rg_rec (rg_close v d.+1 G)
    | rg_msg p G => rg_msg p (rg_close v d G)
    | rg_rcv p G => rg_rcv p (rg_close v d G)
    | rg_alt lb p G => rg_alt lb p (rg_close v d G)
    | rg_brn p Gs => rg_brn p [seq (lG.1, rg_close v d lG.2) | lG <- Gs]
    end.

  Open Scope fset_scope.
  Fixpoint rg_fvar (G : rg_ty) : {fset atom} :=
    match G with
    | rg_var v => Rvar.fvar v
    | rg_rec G
    | rg_msg _ G
    | rg_rcv _ G
    | rg_alt _ _ G => rg_fvar G
    | rg_brn _ Gs => fsetUs [seq rg_fvar lG.2 | lG <- Gs]
    | rg_end => fset0
    end.

  Fixpoint rg_fbvar (d : nat) (G : rg_ty) : {fset nat} :=
    match G with
    | rg_var v => Rvar.fbvar d v
    | rg_rec G  => rg_fbvar d.+1 G
    | rg_msg _ G
    | rg_rcv _ G
    | rg_alt _ _ G => rg_fbvar d G
    | rg_brn _ Gs => fsetUs [seq rg_fbvar d lG.2 | lG <- Gs]
    | rg_end => fset0
    end.

  Definition rg_lc (G : rg_ty) := rg_fbvar 0 G = fset0.
  Notation rgfv a := (rg_var (Rvar.fv a)).
  Notation rgbv a := (rg_var (Rvar.bv a)).

  Lemma in_rgfvar_gfv (a a' : atom) : (a \in rg_fvar (rgfv a')) = (a == a').
  Proof.
    rewrite /rg_fvar; case: fset1P=>[->|].
    - by rewrite eq_refl.
    - by move=> /eqP/negPf->.
  Qed.

  Lemma rgopen_rgfv n X (a : atom) : rg_open n X (rgfv a) = rgfv a.
  Proof. by []. Qed.

  Lemma rgclose_rgfv n X (a : atom) :
    rg_close X n (rgfv a) = if X == a then rgbv n else rgfv a.
  Proof. by rewrite /rg_close/Rvar.close (fun_if rg_var). Qed.

  Lemma rg_open_close X G n :
    X \notin rg_fvar G -> rg_close X n (rg_open n (rgfv X) G) = G.
  Proof.
    elim/rgty_ind2: G n =>//.
    - by move=> v d /= H; rewrite Rvar.open_fun /= (Rvar.open_close d H).
    - move=> G Ih d; rewrite /rg_fvar -/(rg_fvar _)=>/Ih-{Ih}Ih.
      by rewrite -[in RHS](Ih d.+1).
    - move=> p G Ih d; rewrite /rg_fvar -/(rg_fvar _)=>/Ih-{Ih}Ih.
      by rewrite -[in RHS](Ih d).
    - move=> p G Ih d; rewrite /rg_fvar -/(rg_fvar _)=>/Ih-{Ih}Ih.
      by rewrite -[in RHS](Ih d).
    - move=> lb p G Ih d; rewrite /rg_fvar -/(rg_fvar _)=>/Ih-{Ih}Ih.
      by rewrite -[in RHS](Ih d).
    - move=> p Gs /Fa_lift-Ih n; move: (Ih n)=>{Ih}Ih.
      rewrite notin_fold_all -/rg_fvar all_map /preim/=.
      rewrite /SimplPred/= -map_comp/comp/= =>/forallbP/=.
      move=>/(Fa_conj Ih)/Fa_app{Ih}/Fa_map_eq-Ih; congr rg_brn.
      by elim: Gs Ih=>[//|[l G] Gs /= Ih [->/Ih->]].
  Qed.

  Lemma rg_close_open n X G :
    n \notin rg_fbvar 0 G -> rg_open n (rgfv X) (rg_close X n G) = G.
  Proof.
    move: {1 3}n (add0n n)=>n0; elim/rgty_ind2: G 0 n =>///=.
    - by move=> v n n1 <- H; rewrite addnC Rvar.open_fun Rvar.close_open.
    - move=> G Ih d n Eq n_in; congr rg_rec; apply: (Ih d.+1)=>//.
      by rewrite -Eq.
    - by move=> p G Ih d n Eq n_in; congr rg_msg; apply: (Ih d).
    - by move=> p G Ih d n Eq n_in; congr rg_rcv; apply: (Ih d).
    - by move=> lb p G Ih d n Eq n_in; congr rg_alt; apply: (Ih d).
    - move=> p Gs /Fa_lift-Fa d n Eq; rewrite notin_fold_all !all_map /preim/=.
      move: (Fa d)=>{Fa}/Fa_lift/(_ n)/Fa_lift/(_ Eq)-Fa.
      move=>/forallbP/(Fa_conj Fa){Fa}.
      rewrite /SimplPred/= =>/Fa_app/Fa_map_eq-Ih.
      rewrite -map_comp /comp/=; congr rg_brn => {Eq} {d} {n0} {p}.
      by elim: Gs Ih=>[//|/=[l G] Gs Ih [-> /Ih->]].
  Qed.
  Close Scope fset_scope.

  Inductive step : act -> rg_ty -> rg_ty -> Prop :=
  (* Basic rules *)
  | st_msg p G :
      step (a_send p) (rg_msg p G) (rg_rcv p G)
  | st_rcv p G :
      step (a_recv p) (rg_rcv p G) G
  | st_brn (lb : lbl) (p : g_prefix) (K : seq (lbl * rg_ty)) G :
      lookup lb K == Some G ->
      step (a_sel p.1.1 p.1.2 lb) (rg_brn p K) (rg_alt lb p G)
  | st_alt (lb : lbl) (p : g_prefix) G :
      step (a_brn p.1.1 p.1.2 lb) (rg_alt lb p G) G

  (* Asynchronous *)
  | st_amsg a p G G' :
      subject a \notin [:: p.1.1; p.1.2] ->
      step a G G' ->
      step a (rg_msg p G) (rg_msg p G')
  | st_arcv a p G G' :
      subject a != p.1.2 ->
      step a G G' ->
      step a (rg_rcv p G) (rg_rcv p G')
  | st_abrn a p K K' :
      subject a \notin [:: p.1.1; p.1.2] ->
      step_all a K K' ->
      step a (rg_brn p K) (rg_brn p K')
  | st_aalt a lb p G G' :
      subject a != p.1.2 ->
      step a G G' ->
      step a (rg_alt lb p G) (rg_alt lb p G')


  (* Structural *)
  | st_rec l G G' :
      step l (rg_open 0 G (rg_rec G)) G' ->
      step l (rg_rec G)               G'
  with step_all : act -> seq (lbl * rg_ty) -> seq (lbl * rg_ty) -> Prop :=
       | st_nil a : step_all a [::] [::]
       | st_cons a G G' K K' lb :
           step a G G' ->
           step_all a K K' ->
           step_all a ((lb, G) :: K) ((lb, G) :: K')
  .

  Scheme step_ind1 := Induction for step Sort Prop
  with stepall_ind1 := Induction for step_all Sort Prop.

  CoInductive g_lts : trace -> rg_ty -> rg_ty -> Prop :=
  | eg_end : g_lts tr_end rg_end rg_end
  | eg_trans a t G G' G'' :
      step a G G' ->
      g_lts t G' G'' ->
      g_lts (tr_next a t) G G''
  .

End Semantics.

(*
r0 -> r1. r1 -> r0. r1 -> r2. r2 -> r1
C0 < C1
C1 < C0
C1 < C2
C2 < C1

0 - 1 |- 0
      |- 2 - 1

0 - 1 - 0 (c0 + c1)

0 - 1 - 2 (c0 + c1)


[0, 1, 0] [1, 2, 1] [0, 1, 2, 1]

[0,1]
[0,1,0]
[0,1,0] [1,2]
[0,1,0] [1,2,1]

[0, 1, 2] <- 1-0
[0, 1, 0] [1, 2, 1]



                  C0 = C1     | c0   ==== C1 + c0
                  C1 = C0, C2 | c1   ==== C0 + c1 | C2 + c1
                  C2 = C1     | c2   ====

cost C = [r |-> max (cost^C [C(r)])(r) ]_r\in C
cost^C [] [0] = cost^C [(0,c0)] [1]
              = cost^C [(1, c1), (0, c0)] [0, 2]
              = cost^C [(0, c0 + c1), (1, c1)] [2]
              = cost^C [(2, c2), (0, c0 + c1), (1, c1)] [1]
              = cost^C [(2, c2 + c1)]

cost [1,0] (C0, C2 | c1) =
cost [2, 1,0] (C1 | c1) =

 T0 =
 T1 = max (c0 + c1, c1 + c2)
 T2 = max (c0 + c1, c1 + c2)
                  C0 = C1, C0, C2 | c0
                  C1 = C0, C1, C2 | c1
                  C2 = C0, C1 | c2

                  C0 = C0, C1 | c0
                  C1 = C0, C1 | c1
                  C2 = C0, C1 | c2
    C0 + C1 , C0 + C1 , max(C0 + C1, C1 + C2)

T0 = ts + tr + c1 + ts + tr + t0
T1 = ts + tr + c1 + ts + tr + t0
                                T2 = tr + ts + tr + t0 + c1 + ts + tr + c2
*)
